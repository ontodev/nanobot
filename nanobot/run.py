import gadget.sql as gs
import json
import logging
import os
import psycopg2
import traceback

from collections import defaultdict

from flask import (
    abort,
    Blueprint,
    Flask,
    redirect,
    request,
    render_template,
    Response,
    url_for,
)
from gadget.export import dicts2tsv, terms2dicts
from gadget.tree import tree as gadget_tree
from gadget.search import search
from hiccupy import insert_href, render
from html import escape as html_escape
from itertools import chain
from lark import UnexpectedCharacters
from logging import Logger
from sprocket import (
    get_sql_columns,
    get_sql_tables,
    parse_order_by,
    render_database_table,
    render_html_table,
    SprocketError,
)
from sprocket.grammar import PARSER, SprocketTransformer
from sqlalchemy import create_engine
from sqlalchemy.engine import Connection
from sqlalchemy.sql.expression import bindparam
from sqlalchemy.sql.expression import text as sql_text
from typing import Dict, Optional, Tuple, Union
from urllib.parse import unquote
from werkzeug.exceptions import HTTPException

from ontodev_valve import (
    get_matching_values,
    validate_row,
    configure_and_or_load,
    insert_new_row,
    update_row,
)


BUILTIN_LABELS = {
    "rdfs:subClassOf": "parent class",
    "owl:equivalentClass": "equivalent class",
    "owl:disjointWith": "disjoint with",
    "rdfs:subPropertyOf": "parent property",
    "owl:equivalentProperty": "equivalent property",
    "owl:inverseOf": "inverse property",
    "rdfs:domain": "domain",
    "rdfs:range": "range",
    "rdf:type": "type of",
    "owl:sameAs": "same individual",
    "owl:differentFrom": "different individual",
}
FORM_ROW_ID = 0
LOGIC_PREDICATES = [
    "rdfs:subClassOf",
    "owl:equivalentClass",
    "owl:disjointWith",
    "rdfs:subPropertyOf",
    "rdf:type",
    "rdfs:domain",
    "rdfs:range",
]

BLUEPRINT = Blueprint(
    "cmi-pb",
    __name__,
    template_folder=os.path.abspath(os.path.join(os.path.dirname(__file__), "templates")),
)
CONFIG = None  # type: Optional[dict]
PG_CONN = None  # type: Optional[Connection]
SQLITE_CONN = None  # type: Optional[Connection]
LOGGER = None  # type: Optional[Logger]
UPSTREAM_ONTOLOGIES = ["cob", "obi", "uberon", "ncbitaxon"]

OPTIONS = {
    "base_ontology": None,
    "default_params": {},
    "default_table": None,
    "hide_index": False,
    "import_table": None,
    "max_children": 20,
    "synonym": "IAO:0000118",
    "title": "Terminology",
    "tree_predicates": None,
}


@BLUEPRINT.errorhandler(Exception)
def handle_exception(e):
    if isinstance(e, HTTPException):
        return e
    return (
        render_template(
            "template.html",
            project_name=OPTIONS["title"],
            tables=get_display_tables(),
            ontologies=get_display_ontologies(),
            html="<code>" + "<br>".join(traceback.format_exc().split("\n")),
        )
        + "</code>"
    )


@BLUEPRINT.route("/")
def index():
    if OPTIONS["default_table"]:
        return redirect(
            url_for(
                "cmi-pb.table", table_name=OPTIONS["default_table"], **OPTIONS["default_params"]
            )
        )
    return render_template(
        "template.html",
        project_name=OPTIONS["title"],
        html="<h3>Welcome</h3><p>Please select a table</p>",
        tables=get_display_tables(),
        ontologies=get_display_ontologies(),
    )


@BLUEPRINT.route("/<table_name>/row/<row_number>", methods=["GET", "POST"])
def row(table_name, row_number):
    if table_name.casefold() in UPSTREAM_ONTOLOGIES and PG_CONN:
        conn = PG_CONN
    else:
        conn = SQLITE_CONN

    if is_ontology(conn, table_name):
        return abort(400, f"'row' path is not valid for ontology table '{table_name}'")
    try:
        row_number = int(row_number)
    except ValueError:
        return abort(400, f"Row number '{row_number}' must be an integer")
    return render_row_from_database(conn, table_name, None, row_number)


@BLUEPRINT.route("/<table_name>", methods=["GET", "POST"])
def table(table_name):
    if table_name.casefold() in UPSTREAM_ONTOLOGIES and PG_CONN:
        conn = PG_CONN
    else:
        conn = SQLITE_CONN

    messages = defaultdict(list)
    view = request.args.get("view")
    if view == "tree":
        # Will throw an error if non-ontology table
        return render_tree(conn, table_name)

    # Check for subclass of searches - these are automatically term table views
    subclass_of = request.args.get("subClassOf")
    subclass_of_self = request.args.get("subClassOf?")
    descendants_of = request.args.get("subClassOfplus")  # '+' does not work in query params
    descendants_of_self = request.args.get("subClassOf*")

    if subclass_of:
        return render_subclass_of(table_name, "subClassOf", subclass_of)
    elif subclass_of_self:
        return render_subclass_of(table_name, "subClassOf?", subclass_of_self)
    elif descendants_of:
        return render_subclass_of(table_name, "subClassOfplus", descendants_of)
    elif descendants_of_self:
        return render_subclass_of(table_name, "subClassOf*", descendants_of_self)

    # TODO: view=form for tables to add new ontology term

    tables = get_display_tables()

    # First check if table is an ontology table - if so, render term IDs + labels
    if is_ontology(conn, table_name):
        # Maybe get a set of predicates to restrict search results to
        select = request.args.get("select")
        predicates = ["rdfs:label", OPTIONS["synonym"]]
        if select:
            # TODO: add form at top of page for user to select predicates to show?
            pred_labels = select.split(",")
            predicates = gs.get_ids(
                conn, id_or_labels=pred_labels, id_type="predicate", statement=table_name
            )

        search_text = request.args.get("text")
        if search_text or request.args.get("format"):
            # Get matching terms
            if request.args.get("exact") and not request.args.get("format") == "json":
                term_ids = gs.get_ids(conn, id_or_labels=[search_text], statement=table_name)
            else:
                data = search(conn, limit=None, search_text=search_text or "", statement=table_name)
                if request.args.get("format") == "json":
                    # Support for typeahead search
                    return json.dumps(data)
                term_ids = [x["id"] for x in data]
            if len(term_ids) == 1:
                # Single result, redirect to the tree view of that term
                return redirect(
                    url_for("cmi-pb.term", table_name=table_name, term_id=term_ids[0], view="tree")
                )

            # Otherwise, display a table of the results (if they exist)
            if not term_ids:
                return render_template(
                    "template.html",
                    base_ontology=OPTIONS["base_ontology"],
                    import_table=OPTIONS["import_table"],
                    ontologies=get_display_ontologies(),
                    project_name=OPTIONS["title"],
                    show_search=True,
                    subtitle=f"No results for '{search_text}'",
                    table_name=table_name,
                    tables=tables,
                    title=get_ontology_title(conn, table_name),
                )
            data = gs.get_objects(conn, predicates, statement=table_name, term_ids=term_ids)
            response = render_ontology_table(conn, table_name, data, predicates=predicates)
            if isinstance(response, Response):
                return response
            return render_template(
                "template.html",
                base_ontology=OPTIONS["base_ontology"],
                import_table=OPTIONS["import_table"],
                project_name=OPTIONS["title"],
                html=response,
                ontologies=get_display_ontologies(),
                show_search=True,
                subtitle=f"Showing search results for '{search_text}'",
                table_name=table_name,
                tables=tables,
                title=get_ontology_title(conn, table_name),
            )

        # Export the data - excluding anon objects
        data = gs.get_objects(conn, predicates, exclude_json=True, statement=table_name)
        response = render_ontology_table(conn, table_name, data, predicates=predicates)
        if isinstance(response, Response):
            return response
        return render_template(
            "template.html",
            base_ontology=OPTIONS["base_ontology"],
            html=response,
            import_table=OPTIONS["import_table"],
            ontologies=get_display_ontologies(),
            project_name=OPTIONS["title"],
            show_search=True,
            table_name=table_name,
            tables=tables,
            title=get_ontology_title(conn, table_name),
        )

    # Typeahead for autocomplete in data forms
    if request.args.get("format") == "json":
        return get_matching_values(
            json.dumps(CONFIG),
            CONFIG["db"],
            table_name,
            request.args.get("column"),
            matching_string=request.args.get("text"),
        )

    form_html = None
    pk = get_primary_key(table_name)
    cols = get_sql_columns(conn, table_name)
    if request.method == "POST":
        # Override view, which isn't passed in POST
        view = "form"
        # Use the cols from the table, in case a value wasn't given to something
        # - we always ignore meta columns & row_number (for new row)
        new_row = {}
        for c in cols:
            if c.endswith("_meta") or c == "row_number":
                continue
            v = request.form.get(c)
            if not v:
                # Check for "other"
                v = request.form.get(c + "_other", "")
            new_row[c] = v

        validated_row = validate_table_row(table_name, new_row)
        if request.form["action"] == "validate":
            form_html = get_row_as_form(table_name, validated_row)
        elif request.form["action"] == "submit":
            # Add row to the database and get the new row number
            row_number = insert_new_row(CONFIG["db"], table_name, json.dumps(validated_row))
            # Use row number to get the primary key for this row & redirect to new term
            if pk == "row_number":
                row_pk = row_number
            else:
                res = conn.execute(
                    sql_text(
                        f"""SELECT DISTINCT "{pk}" from "{table_name}_view"
                        WHERE row_number = :row_number"""
                    ),
                    row_number=row_number,
                ).fetchone()
                if res and res[pk]:
                    row_pk = res[pk]
                else:
                    # This row does not have a primary key, meaning it is a conflict
                    # Use "row" format for URL
                    row_pk = f"row/{row_number}"
            return redirect(url_for("cmi-pb.term", table_name=table_name, term_id=row_pk))

    if view == "form":
        if not form_html:
            # Some values may be filled in from request args, otherwise values are blank
            row = {c: request.args.get(c) for c in cols if c != "row_number"}
            form_html = get_row_as_form(table_name, row)
        return render_template(
            "data_form.html",
            base_ontology=OPTIONS["base_ontology"],
            import_table=OPTIONS["import_table"],
            project_name=OPTIONS["title"],
            messages=messages,
            ontologies=get_display_ontologies(),
            row_form=form_html,
            table_name=table_name,
            tables=tables,
            title=f'Add row to <a href="{url_for("cmi-pb.table", table_name=table_name)}">{table_name}</a>',
        )

    # Otherwise render default sprocket table
    try:
        response = render_database_table(
            conn,
            table_name,
            request.args,
            base_url=url_for("cmi-pb.table", table_name=table_name),
            display_messages=messages,
            edit_link=unquote(
                url_for("cmi-pb.term", table_name=table_name, term_id="{row_id}", view="form")
            ),
            ignore_cols=["row_number"],
            ignore_params=["project-name", "branch-name", "view-path"],
            primary_key=pk,
            show_help=True,
            standalone=False,
            transform=get_transformations(table_name),
            use_view=True,
        )
    except SprocketError as e:
        return abort(422, str(e))
    if isinstance(response, Response):
        return response
    return render_template(
        "template.html",
        add_btn={
            "text": "New row",
            "url": url_for("cmi-pb.table", table_name=table_name, view="form"),
        },
        base_ontology=OPTIONS["base_ontology"],
        html=response,
        import_table=OPTIONS["import_table"],
        project_name=OPTIONS["title"],
        table_name=table_name,
        tables=get_display_tables(),
        ontologies=get_display_ontologies(),
        title=table_name,
    )


@BLUEPRINT.route("/<table_name>/<term_id>", methods=["GET", "POST"])
def term(table_name, term_id):
    if table_name.casefold() in UPSTREAM_ONTOLOGIES and PG_CONN:
        conn = PG_CONN
    else:
        conn = SQLITE_CONN

    if not is_ontology(conn, table_name):
        # Get row number based on PK
        row_number = get_row_number(table_name, term_id)
        if not row_number:
            return abort(
                500, f"'{term_id}' is not a valid primary key value for table '{table_name}'"
            )
        return render_row_from_database(conn, table_name, term_id, row_number)

    # Redirect to main ontology table search, do not limit search results
    search_text = request.args.get("text")
    if search_text:
        return redirect(url_for("cmi-pb.table", table_name=table_name, text=search_text))

    view = request.args.get("view")
    if view == "form":
        # TODO: implement editing ontology term from database
        # No template for this term -- show form for ontology term
        # return render_term_form(table_name, term_id)
        return abort(501, "Editing ontology terms is not yet implemented")
    elif view == "tree":
        return render_tree(conn, table_name, term_id=term_id)
    elif request.args.get("format") == "json":
        return dump_search_results(table_name)
    else:
        select = request.args.get("select")
        if select:
            # TODO: add form at top of page for user to select predicates to show?
            pred_labels = select.split(",")
            predicates = gs.get_ids(
                conn, id_or_labels=pred_labels, id_type="predicate", statement=table_name
            )
        else:
            predicates = gs.get_ids(conn, id_type="predicate", statement=table_name)

        data = gs.get_objects(
            conn, predicates, include_all_predicates=False, statement=table_name, term_ids=[term_id]
        )
        lbls = data[term_id].get("rdfs:label")
        subtitle = lbls[0]["object"] if lbls else term_id

        response = render_ontology_table(conn, table_name, data, predicates=predicates)
        if isinstance(response, Response):
            return response

        # Determine if we need to include add/edit buttons
        add_btn = None
        edit_btn = None
        term_loc = get_term_location(term_id)
        if term_loc:
            edit_btn = {
                "text": "Edit term in " + term_loc,
                "url": url_for("cmi-pb.term", table_name=term_loc, term_id=term_id,
                               view="form"),
            }
            if table_name == OPTIONS["base_ontology"] and term_loc != OPTIONS["import_table"]:
                # Always include an add button which adds a new term in same template
                add_btn = {
                    "text": "New term in " + term_loc,
                    "url": url_for("cmi-pb.table", table_name=term_loc, view="form"),
                }
        elif table_name != OPTIONS["base_ontology"] and OPTIONS["import_table"]:
            # Only include add button if its not already in import
            term_label = gs.get_labels(conn, [term_id], statement=table_name)[term_id]
            url_args = {
                "table_name": OPTIONS["import_table"],
                "view": "form",
                "Source": table_name,
                "ID": term_id,
                "Label": term_label,
            }
            add_btn = {
                "text": "Add to " + OPTIONS["base_ontology"],
                "url": url_for("cmi-pb.table", **url_args),
            }

        return render_template(
            "template.html",
            add_btn=add_btn,
            base_ontology=OPTIONS["base_ontology"],
            edit_btn=edit_btn,
            import_table=OPTIONS["import_table"],
            project_name=OPTIONS["title"],
            html=response,
            ontologies=get_display_ontologies(),
            show_search=True,
            subtitle=subtitle,
            table_name=table_name,
            tables=get_display_tables(),
            title=get_ontology_title(conn, table_name, term_id=term_id),
        )


def flatten(lst: list) -> list:
    """Flatten a nested list.

    :param lst: nested list to flatten
    :return: flat list
    """
    for el in lst:
        if isinstance(el, list) and not isinstance(el, (str, bytes)):
            yield from flatten(el)
        else:
            yield el


def get_display_ontologies() -> list:
    """Return a list of ontology tables from all database tables to display in navigation.

    :return: list of ontology tables
    """
    return [t for t in get_sql_tables(SQLITE_CONN) if is_ontology(SQLITE_CONN, t)] + UPSTREAM_ONTOLOGIES


def get_display_tables() -> list:
    """Return a list of data tables to display in navigation.

    :return: list of data tables
    """
    term_index = get_term_index()
    if term_index and OPTIONS["hide_index"]:
        tables = [x for x in get_sql_tables(SQLITE_CONN) if x != term_index]
    else:
        tables = get_sql_tables(SQLITE_CONN)
    return [t for t in tables if not is_ontology(SQLITE_CONN, t)]


def get_term_index() -> Union[str, None]:
    """Get the table of type 'index'.

    :return: table name of index table, or None
    """
    res = SQLITE_CONN.execute('SELECT "table" FROM "table" WHERE "type" = \'index\'').fetchone()
    if res:
        return res["table"]
    return None


def get_term_location(term_id: str) -> Union[str, None]:
    """Return the source table for an ontology term ID, where the term exists in the term index.

    :param term_id: ontology term to get source table of
    :return: source table, or None
    """
    term_index = get_term_index()
    if term_index:
        res = SQLITE_CONN.execute(
            sql_text(f'SELECT "table" FROM "{term_index}" WHERE ID == :term_id'), term_id=term_id,
        ).fetchone()
        if res:
            return res["table"]
    return None


# ----- DATA TABLE METHODS -----


def get_all_datatypes(datatype: str) -> list:
    """Given a datatype, get all ancestor datatypes from the 'datatype' table.

    :param datatype: datatype to get all ancestor datatypes of
    :return: all ancestor datatypes of given datatype (inclusive of given datatype)
    """
    query = sql_text(
        """WITH RECURSIVE ancestors(child, parent) AS (
            SELECT DISTINCT
                :dt AS child,
                parent AS parent
            FROM datatype
            WHERE datatype = :dt
            UNION
            SELECT
                datatype AS child,
                datatype.parent AS parent
            FROM datatype, ancestors
            WHERE ancestors.parent = datatype)
        SELECT DISTINCT parent FROM ancestors"""
    )
    results = SQLITE_CONN.execute(query, dt=datatype)
    all_types = [datatype]
    for res in results:
        all_types.append(res["parent"])
    return all_types


def get_hiccup_form_row(
    header: str,
    allow_delete: bool = False,
    allowed_values: list = None,
    annotations: dict = None,
    description: str = None,
    display_header: str = None,
    html_type: str = "text",
    message: str = None,
    readonly: bool = False,
    valid: Optional[bool] = None,
    value: str = None,
) -> list:
    """Create a hiccup-style list for a form row.

    :param header: header name for this row
    :param allow_delete: if True, include an 'x' button to remove the row (used in ontology forms)
    :param allowed_values: a list of allowed values for select, radio, and checkbox form fields
    :param annotations: dict of predicate -> values for annotations on a predicate-object pair (used in ontology forms)
    :param description: if included, generate a tooltip containing this description for the field
    :param display_header: if the label of the form field differs from the header, use this param to set what should be
                           shown in the form. The 'header' is used to pass the value in the POST request.
    :param html_type: the type of form field (text, select, radio, checkbox, search, textarea, number)
    :param message: a validation message to include under the form field
    :param readonly: if True, make the form field non-editable
    :param valid: if False, set the form field to 'is-invalid', which displays an error in the HTML form. If True, set
                  the form field to 'is-valid', which shows that the field passed validation. If None, do not add a
                  validation class to the form field.
    :param value: optional value to set the form field to
    :return: hiccup-style list for the form row
    """
    # TODO: support other HTML types: dropdown, boolean, etc...
    # TODO: handle datatypes for ontology forms (include_datatypes?)
    global FORM_ROW_ID

    if html_type in ["select", "radio", "checkbox"] and not allowed_values:
        # TODO: error handling - allowed_values should always be included for these
        raise Exception(f"A list of allowed values is required for HTML type '{html_type}'")

    # Create the header label for this form row
    header_col = ["div", {"class": "col-md-3", "id": FORM_ROW_ID}]
    if allow_delete:
        header_col.append(
            [
                "a",
                {"href": f"javascript:del({FORM_ROW_ID})"},
                ["i", {"class": "bi-x-circle", "style": "font-size: 16px; color: #dc3545;"}],
                "&nbsp",
            ]
        )
    FORM_ROW_ID += 1
    if display_header:
        header_col.append(["b", display_header])
    else:
        header_col.append(["b", header])
    if description:
        # Add a ? tooltip that displays description on hover
        header_col.append(
            [
                "button",
                {
                    "class": "btn",
                    "data-bs-toggle": "tooltip",
                    "data-bs-placement": "right",
                    "title": description,
                },
                ["i", {"class": "bi-question-circle"}],
            ]
        )

    # Create the value input for this form row
    classes = []
    if valid:
        classes.append("is-valid")
    elif valid is not None:
        classes.append("is-invalid")

    input_attrs = {}
    if readonly:
        # No name so that it isn't passed through POST data
        input_attrs["readonly"] = True
    else:
        # Everything else uses the header as the element name
        input_attrs["name"] = header

    value_col = ["div", {"class": "col-md-9 form-group"}]
    if html_type == "textarea":
        classes.insert(0, "form-control")
        input_attrs["class"] = " ".join(classes)
        textarea_element = ["textarea", input_attrs]
        if value:
            textarea_element.append(html_escape(value))
        value_col.append(textarea_element)

    elif html_type == "select":
        # TODO: what if value is not in allowed_values?
        classes.insert(0, "form-select")
        input_attrs["class"] = " ".join(classes)
        select_element = ["select", input_attrs]
        has_selected = False
        for av in allowed_values:
            av_safe = html_escape(str(av))
            if value and str(av) == str(value):
                has_selected = True
                select_element.append(
                    ["option", {"value": html_escape(av_safe), "selected": True}, av_safe]
                )
            else:
                select_element.append(["option", {"value": html_escape(av_safe)}, av_safe])
        # Add an empty string for no value at the start of the options
        if has_selected:
            select_element.insert(2, ["option", {"value": ""}])
        else:
            # If there is currently no value, make sure this one is selected
            select_element.insert(2, ["option", {"value": "", "selected": True}])
        value_col.append(select_element)

    elif html_type in ["text", "number", "search"]:
        # TODO: support a range restriction for 'number'
        classes.insert(0, "form-control")
        input_attrs["type"] = html_type
        if html_type == "search":
            classes.extend(["search", "typeahead"])
            input_attrs["id"] = f"{header}-typeahead-form"
        input_attrs["class"] = " ".join(classes)
        if value:
            input_attrs["value"] = html_escape(str(value))
        value_col.append(["input", input_attrs])

    elif html_type == "radio":
        # TODO: what if value is not in allowed_values? Or what if there is no value?
        classes.insert(0, "form-check-input")
        input_attrs["type"] = html_type
        input_attrs["class"] = " ".join(classes)
        validation_cls = None
        for av in allowed_values:
            av_safe = html_escape(str(av))
            attrs_copy = input_attrs.copy()
            attrs_copy["value"] = av_safe
            if value and str(av) == str(value):
                attrs_copy["checked"] = True
            value_col.append(
                [
                    "div",
                    ["input", attrs_copy],
                    ["label", {"class": "form-check-label", "for": av_safe}, av_safe],
                ]
            )
        if message:
            validation_cls = "invalid-feedback"
            if valid:
                validation_cls = "valid-feedback"
        attrs_copy = input_attrs.copy()
        attrs_copy["value"] = ""
        input_attrs = {
            "type": "text",
            "class": "form-control",
            "name": header + "_other",
            "placeholder": "other",
        }
        if value and value not in allowed_values:
            attrs_copy["checked"] = True
            input_attrs["value"] = value
        e = [
            "div",
            ["input", attrs_copy],
            ["label", {"class": "form-check-label", "for": "other"}, ["input", input_attrs]],
        ]
        if validation_cls:
            # Only add validation message to the last form-check element
            e.append(["div", {"class": validation_cls}, message])
        value_col.append(e)

    else:
        raise abort(500, f"'{html_type}' form field is not supported for column {header}.")

    if message and html_type != "radio":
        # We already added the message to the radio type; needs to be embedded in radio ele
        cls = "invalid-feedback"
        if valid:
            cls = "valid-feedback"
        value_col.append(["div", {"class": cls}, message])
    if annotations:
        # TODO: support input types for annotations - text, textarea, search...
        ann_html = []
        for ann_pred, ann_values in annotations.items():
            for av in ann_values:
                # TODO: add delete button FORM_ROW_ID-annotation-X
                av = av["object"]
                ann_html = [
                    "div",
                    {
                        "class": "row justify-content-end",
                        "style": "padding-right: 0px; padding-top: 5px;",
                    },
                    [
                        "div",
                        {"class": "col-sm-9"},
                        [
                            "div",
                            {"class": "row"},
                            [
                                "label",
                                {
                                    "class": "col-sm-2 col-form-label",
                                    "style": "padding-left: 20px !important;",
                                },
                                ann_pred,
                            ],
                            [
                                "div",
                                {"class": "col-sm-10", "style": "padding-right: 0px !important;"},
                                [
                                    "input",
                                    {
                                        "type": "text",
                                        "class": "form-control",
                                        "value": av.replace('"', "&quot;"),
                                    },
                                ],
                            ],
                        ],
                    ],
                ]
        value_col.append(ann_html)

    return ["div", {"class": "row py-1"}, header_col, value_col]


def get_html_type_and_values(datatype: str, values: list = None) -> Tuple[Optional[str], Optional[list]]:
    """Query the 'datatype' table for the HTML form field type and, maybe, a list of allowed values for the field.

    :param datatype: datatype to get HTML type and allowed values of
    :param values: allowed values from column (overrides datatype values)
    :return: tuple of HTML type and allowed values for given datatype
    """
    res = SQLITE_CONN.execute(
        'SELECT parent, "HTML type", condition FROM datatype WHERE datatype = :datatype',
        datatype=datatype,
    ).fetchone()
    if res:
        if not values:
            condition = res["condition"]
            if condition and condition.startswith("in(") and condition.endswith(")"):
                values = [c.strip("'\" ") for c in condition[3:-1].split(",")]
        html_type = res["HTML type"]
        if html_type:
            return html_type, values
        parent = res["parent"]
        if parent:
            return get_html_type_and_values(parent, values=values)
    return None, None


def get_messages(data: dict) -> Dict[str, list]:
    """Extract messages from a validated row into a dictionary of messages.

    :param data: row data from database
    :return: dict of message level -> list of messages at that level
    """
    messages = defaultdict(list)
    for header, details in data.items():
        if header == "row_number":
            continue
        if details["messages"]:
            for msg in details["messages"]:
                if msg["level"] == "error":
                    if "error" not in messages:
                        messages["error"] = list()
                    messages["error"].append(msg["message"])
                elif msg["level"] == "warn":
                    if "warn" not in messages:
                        messages["warn"] = list()
                    messages["warn"].append(msg["message"])
                elif msg["level"] == "info":
                    if "info" not in messages:
                        messages["info"] = list()
                    messages["info"].append(msg["message"])
    return messages


def get_primary_key(table_name: str) -> str:
    """Retrieve the primary key for a given table. Otherwise, 'row_number' is used as the primary key.

    :param table_name: table to get primary key of
    :return: primary key or 'row_number'
    """
    query = sql_text(
        'SELECT "column" FROM "column" WHERE "table" = :table AND "structure" LIKE \'%%primary%%\''
    )
    res = SQLITE_CONN.execute(query, table=table_name).fetchone()
    if res:
        return res["column"]
    else:
        return "row_number"


def get_row_as_form(table_name: str, data: dict) -> str:
    """Transform a row either from query results or validation into an editable HTML form.

    :param table_name: source table for row
    :param data: row data from table
    :return: string HTML for editable form for this row
    """
    html = ["form", {"method": "post"}]
    row_valid = None

    for header, value in data.items():
        if header == "row_number" or header.endswith("_meta"):
            continue

        # Get the details from the value,
        # which is either a JSON object (from validation) or a literal
        valid = None
        message = None
        if value and isinstance(value, dict):
            # This row is coming from a validated row
            message = "<br>".join({x["message"] for x in value["messages"]})
            valid = value["valid"]
            if valid and row_valid is None:
                row_valid = True
            elif not valid:
                row_valid = False
            value = value["value"]
        else:
            # This row is coming from a query result
            # Check for meta row
            meta_row = data.get(header + "_meta")
            if meta_row:
                meta = json.loads(meta_row)
                if meta.get("value"):
                    value = meta["value"]
            if not value:
                # If value is still None, we couldn't find nulltype or invalid value
                value = ""

        desc = None
        # Default HTML type is a simple text input
        html_type = "text"
        allowed_values = None
        tables = get_sql_tables(SQLITE_CONN)
        if "column" in tables:
            # Use column table to get description & datatype for this col
            res = SQLITE_CONN.execute(
                sql_text(
                    """SELECT description, datatype, structure FROM "column"
                    WHERE "table" = :table AND "column" = :column"""
                ),
                table=table_name,
                column=header,
            ).fetchone()
            if res:
                desc = res["description"]
                datatype = res["datatype"]
                structure = res["structure"]
                if structure and structure.split("(")[0] in ["from", "in", "tree", "under"]:
                    # Given the from structure, we always turn the input into a search
                    html_type = "search"
                elif datatype and "datatype" in tables:
                    # Everything else uses an HTML type defined in the datatype table
                    # If a datatype does not have an HTML type, search for first ancestor type
                    html_type, allowed_values = get_html_type_and_values(datatype)
        if allowed_values and not html_type:
            # Default to search when allowed_values are provided
            # This will still allow users to input invalid values
            html_type = "search"

        readonly = False
        if html_type == "readonly":
            html_type = "text"
            readonly = True

        # Add the hiccup vector for this field as a Bootstrap row containing form elements
        html.append(
            get_hiccup_form_row(
                header,
                allowed_values=allowed_values,
                description=desc,
                html_type=html_type,
                message=message,
                readonly=readonly,
                valid=valid,
                value=value,
            )
        )

    if row_valid:
        # All fields passed validation - display green button
        submit_cls = "success"
    elif row_valid is not None:
        # One or more fields failed validation - display red button
        submit_cls = "danger"
    else:
        # Row has not yet been validated - display gray button
        submit_cls = "secondary"
    html.append(
        [
            "div",
            {"class": "row", "style": "padding-top: 10px;"},
            [
                "div",
                {"class": "col-auto"},
                [
                    "button",
                    {
                        "type": "submit",
                        "name": "action",
                        "value": "validate",
                        "class": "btn btn-large btn-outline-primary",
                    },
                    "Validate",
                ],
            ],
            [
                "div",
                {"class": "col-auto"},
                [
                    "button",
                    {
                        "type": "submit",
                        "name": "action",
                        "value": "submit",
                        "class": f"btn btn-large btn-outline-{submit_cls}",
                    },
                    "Submit",
                ],
            ],
        ]
    )
    return render(html)


def get_row_number(table_name: str, pk_value: str) -> Optional[int]:
    """Given a table name and the value of a primary key, return the row number for the row with that primary key value.

    :param table_name: table to get row number from
    :param pk_value: primary key value for row to get row number of
    :return: row number for row with given primary key, or None if primary key is not found
    """
    pk_col = get_primary_key(table_name)
    res = SQLITE_CONN.execute(
        sql_text(f'SELECT row_number FROM "{table_name}" WHERE "{pk_col}" = :pk'), pk=pk_value
    ).fetchone()
    if not res:
        return None
    return int(res["row_number"])


def get_transformations(table_name: str) -> dict:
    """Get display value transformations for all columns given table. These are used to create links for ontology terms
    from templates to the tree browser.

    :param table_name: table to get any value transformations of
    :return: dict of column name -> transformation
    """
    transform = {}
    cols = get_sql_columns(SQLITE_CONN, table_name)
    if not(cols):
        return abort(400, f"No columns found for table '{table_name}'. Does '{table_name}' exist?")

    query = sql_text(
        f'SELECT "column", "datatype" FROM "column" WHERE "table" = :t AND "column" IN :cols'
    ).bindparams(bindparam("cols", expanding=True))
    results = SQLITE_CONN.execute(query, t=table_name, cols=cols).fetchall()
    for res in results:
        dt = res["datatype"]
        col = res["column"]
        all_types = get_all_datatypes(dt)
        # Currently we are only transforming ontology_id to tree links
        if "split_ontology_id" in all_types:
            url_pat = (
                unquote(
                    url_for(
                        "cmi-pb.term",
                        table_name=OPTIONS["base_ontology"],
                        term_id="TERM",
                        view="tree",
                    )
                )
                .replace("+", " ")
                .replace("TERM", "''' + c + '''")
            )
            transform[
                col
            ] = f""""|".join(
            [f'''<a href="{url_pat}">''' + c + "</a>" for c in '''{{{col}}}'''.split('|')])"""
        elif "split_ontology_label" in all_types:
            url_pat = (
                unquote(
                    url_for(
                        "cmi-pb.table",
                        table_name=OPTIONS["base_ontology"],
                        text="TERM",
                        exact="true",
                    )
                )
                .replace("+", " ")
                .replace("TERM", "''' + c + '''")
            )
            transform[
                col
            ] = f""""|".join(
            [f'''<a href="{url_pat}">''' + c + "</a>" for c in '''{{{col}}}'''.split('|')])"""
        elif "ontology_id" in all_types:
            url_pat = unquote(
                url_for(
                    "cmi-pb.term",
                    table_name=OPTIONS["base_ontology"],
                    term_id=f"{{{col}}}",
                    view="tree",
                )
            ).replace("+", " ")
            transform[col] = f'''"""<a href="{url_pat}">{{{col}}}</a>"""'''
        elif "ontology_label" in all_types:
            url_pat = unquote(
                url_for(
                    "cmi-pb.table",
                    table_name=OPTIONS["base_ontology"],
                    text=f"{{{col}}}",
                    exact="true",
                )
            ).replace("+", " ")
            transform[col] = f'''"""<a href="{url_pat}">{{{col}}}</a>"""'''
    return transform


def render_row_from_database(conn, table_name: str, term_id: str, row_number: int) -> Optional[Response]:
    """Render the data from a row in a database using query parameters. If a format is not specified, an HTML string is
    returned. Otherwise, the data in given format is returned as a Response object for the client to download.

    :param table_name: table that the row exists in
    :param term_id: primary key of row
    :param row_number: row number of row
    :return: HTML string or Response
    """
    view = request.args.get("view")
    messages = None
    form_html = None
    if request.method == "POST":
        # Use the cols from the table, in case a value wasn't given to something
        # - we always ignore meta columns & row_number (for new row)
        new_row = {}
        for c in get_sql_columns(conn, table_name):
            if c.endswith("_meta") or c == "row_number":
                continue
            v = request.form.get(c)
            if not v:
                # Check for "other"
                v = request.form.get(c + "_other", "")
            new_row[c] = v

        # Manually override view, which is not included in request.args in CGI app
        view = "form"
        if request.form["action"] == "validate":
            validated_row = validate_table_row(table_name, new_row, row_number=row_number)
            # Place row_number first
            validated_row_2 = {"row_number": row_number}
            validated_row_2.update(validated_row)
            validated_row = validated_row_2
            form_html = get_row_as_form(table_name, validated_row)
        elif request.form["action"] == "submit":
            # First validate the row to get the meta columns
            validated_row = validate_table_row(table_name, new_row, row_number=row_number)
            # Update the row regardless of results
            # Row ID may be different than row number, if exists
            update_row(CONFIG["db"], table_name, json.dumps(validated_row), row_number)
            messages = get_messages(validated_row)
            if messages.get("error"):
                warn = messages.get("warn", [])
                warn.append(f"Row updated with {len(messages['error'])} errors")
                messages["warn"] = warn
            else:
                messages["success"] = ["Row successfully updated!"]

    if view == "form":
        if not form_html:
            # Get the row
            res = dict(
                conn.execute(
                    f"SELECT * FROM {table_name}_view WHERE row_number = {row_number}"
                ).fetchone()
            )
            form_html = get_row_as_form(table_name, res)

        if not form_html:
            return abort(500, "something went wrong - unable to render form")

        if term_id:
            table_url = url_for("cmi-pb.term", table_name=table_name, term_id=term_id)
        else:
            table_url = url_for("cmi-pb.row", table_name=table_name, row_number=row_number)
        return render_template(
            "data_form.html",
            base_ontology=OPTIONS["base_ontology"],
            base_url=url_for("cmi-pb.table", table_name=table_name),
            import_table=OPTIONS["import_table"],
            project_name=OPTIONS["title"],
            messages=messages,
            ontologies=get_display_ontologies(),
            row_form=form_html,
            subtitle=f'<a href="{table_url}">Return to row</a>',
            table_name=table_name,
            tables=get_display_tables(),
            title=f'Update row in <a href="{url_for("cmi-pb.table", table_name=table_name)}">{table_name}</a>',
        )

    # Set the request.args to be in the format sprocket expects (like swagger)
    request_args = request.args.to_dict()
    request_args["offset"] = str(row_number - 1)
    request_args["limit"] = "1"

    try:
        response = render_database_table(
            conn,
            table_name,
            request_args,
            base_url=url_for("cmi-pb.table", table_name=table_name),
            edit_link=unquote(
                url_for("cmi-pb.term", table_name=table_name, term_id="{row_id}", view="form")
            ),
            ignore_cols=["row_number"],
            ignore_params=["project-name", "branch-name", "view-path"],
            primary_key=get_primary_key(table_name),
            show_help=True,
            standalone=False,
            transform=get_transformations(table_name),
            use_view=True,
        )
    except SprocketError as e:
        return abort(422, str(e))
    if isinstance(response, Response):
        return response
    return render_template(
        "template.html",
        base_ontology=OPTIONS["base_ontology"],
        edit_btn={
            "text": "Edit row",
            "url": url_for("cmi-pb.term", table_name=table_name, term_id=term_id),
        },
        import_table=OPTIONS["import_table"],
        project_name=OPTIONS["title"],
        html=response,
        ontologies=get_display_ontologies(),
        table_name=table_name,
        tables=get_display_tables(),
        title=f'Viewing row in <a href="{url_for("cmi-pb.table", table_name=table_name)}">{table_name}</a>',
    )


def validate_table_row(table_name: str, data: dict, row_number: int = None) -> dict:
    """Perform validation on a row.

    :param table_name: source table
    :param data: row data from source table
    :param row_number: row number of row, or None for a new row
    :return: validated row
    """
    # Transform row into dict expected for validate
    result_row = {}
    for column, value in data.items():
        result_row[column] = {
            "value": value,
            "valid": True,
            "messages": [],
        }

    # Row number may be different than row ID, if this column is used
    validated_row = validate_row(
        json.dumps(CONFIG),
        CONFIG["db"],
        table_name,
        json.dumps(result_row),
        True if row_number else False,
        row_number if row_number else None,
    )
    return json.loads(validated_row)


# ----- ONTOLOGY TABLE METHODS -----


def dump_search_results(table_name: str) -> str:
    """Return the ontology term search results as a JSON string. Flask request.args are used to get the search text.

    :param table_name: table to search in
    :return: search results
    """
    search_text = request.args.get("text")
    if not search_text:
        return json.dumps([])
    # return the raw search results to use in typeahead
    return json.dumps(
        search(SQLITE_CONN, limit=30, search_text=search_text, statement=table_name)
    )


def get_ontology_title(conn, table_name: str, table_active: bool = True, term_id: str = None) -> str:
    """Given an ontology statement table, get the ontology title element which includes the ontology title and a link to
    tree and table views.

    :param table_name: ontology statement table
    :param table_active: if True, the active page is the 'table' page
    :param term_id: current term ID, if on a term
    :return: string HTML element
    """
    # Try to get an ontology title using the dce:title property
    ontology_title = None
    ontology_iri = gs.get_ontology_iri(conn, statement=table_name)
    if ontology_iri:
        prefixes = gs.get_prefixes(conn)
        ontology_title = gs.get_ontology_title(conn, prefixes, ontology_iri, statement=table_name)

    # Create the links
    if term_id:
        table_url = url_for("cmi-pb.term", table_name=table_name, term_id=term_id)
        tree_url = url_for("cmi-pb.term", table_name=table_name, term_id=term_id, view="tree")
    else:
        table_url = url_for("cmi-pb.table", table_name=table_name)
        tree_url = url_for("cmi-pb.table", table_name=table_name, view="tree")

    # Return the HTML element with title & buttons for tree/table view
    if table_active:
        table_class = "btn btn-sm btn-outline-primary active"
        tree_class = "btn btn-sm btn-outline-primary"
    else:
        table_class = "btn btn-sm btn-outline-primary"
        tree_class = "btn btn-sm btn-outline-primary active"
    return render(
        [
            "div",
            {"class": "d-flex justify-content-between align-items-center"},
            ["div", ontology_title or table_name],
            [
                "div",
                {"class": "btn-group", "style": "display: inline-table !important;"},
                ["a", {"href": table_url, "class": table_class}, "Table"],
                ["a", {"href": tree_url, "class": tree_class}, "Tree"],
            ],
        ]
    )


def get_terms_from_arg(table_name: str, arg: str) -> dict:
    """Using a Swagger-like query parameter, get a dict of the ontology term IDs -> labels matched by that arg.

    :param table_name: ontology statement table to search for IDs and labels
    :param arg: Swagger-like arg (e.g. like.%foo%)
    :return: dict of term ID -> label for each term matched by the arg
    """
    try:
        parsed = PARSER.parse(arg)
        res = SprocketTransformer().transform(parsed)
        if res[0] != "in":
            raise ValueError(f"Operator must be 'in', not '{res[0]}'")
        parent_terms = res[1]
    except UnexpectedCharacters:
        parent_terms = [arg]
    # We don't know if we were passed ID or label, so get both for all terms
    return gs.get_labels(SQLITE_CONN, parent_terms, statement=table_name)


def get_terms_of_type(table_name: str, entity_type: str) -> list:
    """Get all ontology terms of a given entity type.

    :param table_name: ontology statement table
    :param entity_type: entity to get all instances of
    :return: list of ontology terms of given type
    """
    results = SQLITE_CONN.execute(
        sql_text(
            f"SELECT subject FROM \"{table_name}\" WHERE predicate = 'rdf:type' AND object = :type"
        ),
        type=entity_type,
    ).fetchall()
    return [res["subject"] for res in results]


def is_ontology(conn, table_name: str) -> bool:
    """Check if a given table is an LDTab ontology statement table.

    :param table_name: table to check
    :return: True if table is an LDTab ontology statement table"""
    columns = get_sql_columns(conn, table_name)
    return {"subject", "predicate", "object", "datatype", "annotation"}.issubset(set(columns))


def render_ontology_table(conn, table_name, data, predicates: list = None) -> Optional[Response]:
    """Render an ontology statement table as a Response for downloads or an HTML table (string).

    :param table_name: name of SQL table that contains terms
    :param data: data to render - dict of term ID -> predicate ID -> list of JSON objects
    :param predicates: list of predicate IDs - if not provided, predicate IDs are taken from data
    :return: Response or HTML string
    """
    # TODO: do we care about displaying annotations in this table view? Or only on term view?
    # Reverse the ID -> label dictionary to translate column names to IDs
    if not predicates:
        predicates = set(chain.from_iterable([list(x.keys()) for x in data.values()]))
    predicate_labels = gs.get_labels(conn, list(predicates), statement=table_name)

    # TODO: how do we want to handle these? Sometimes they are URNs, e.g. swrl
    # Exclude full IRIs
    data = {k: v for k, v in data.items() if not k.startswith("<")}

    # Order based on raw value of 'object', don't worry about rendering
    if request.args.get("order"):
        label_to_id = {v: k for k, v in predicate_labels.items()}
        order_by = parse_order_by(request.args["order"])
        for ob in order_by:
            reverse = False
            if ob["order"] == "desc":
                reverse = True

            if ob["key"] == "ID":
                # ID is never null
                # sorted is more efficient here so we don't need to turn dict into list of tuples
                data = {k: v for k, v in sorted(data.items(), reverse=reverse)}
                continue

            key = label_to_id.get(ob["key"], ob["key"])  # e.g., rdfs:label

            # Separate out the items with no list entries for this predicate
            nulls = {k: v for k, v in data.items() if not v[key]}
            non_nulls = [[k, v] for k, v in data.items() if v[key]]

            # Sort the items with entries for this predicate
            non_nulls.sort(key=lambda itm: itm[1][key][0]["object"], reverse=reverse)

            # ... then put the nulls in the correct spot
            if ob["nulls"] == "first":
                data = nulls
                data.update({k: v for k, v in non_nulls})
            else:
                data = {k: v for k, v in non_nulls}
                data.update(nulls)

    # Offset and limit used to determine which terms to render
    # Rendering objects for all terms is very slow
    offset = int(request.args.get("offset", "0"))
    limit = int(request.args.get("limit", "100")) + offset

    data = [[k, v] for k, v in data.items()]
    data_subset = {k: v for k, v in data[offset:limit]}
    post_subset = {k: v for k, v in data[limit:]}
    data = {k: v for k, v in data[:offset]}

    fmt = request.args.get("format")
    if not fmt:
        # Convert objects to hiccup with ofn
        rendered = terms2dicts(
            conn,
            data_subset,
            include_annotations=True,
            include_id=True,
            rdfa=True,
            statement=table_name,
        )
        for itm in rendered:
            # Render using hiccup module
            rendered_term = {}
            term_id = itm["ID"]
            for predicate_id, hiccup in itm.items():
                if hiccup:
                    if predicate_id == "ID":
                        hiccup = ["a", {"resource": hiccup}, hiccup]
                    hiccup = insert_href(
                        hiccup,
                        href=unquote(
                            url_for("cmi-pb.term", table_name=table_name, term_id="{curie}")
                        ),
                    )
                    rendered_term[predicate_id] = render(hiccup)
                else:
                    rendered_term[predicate_id] = None
            data[term_id] = rendered_term
        data.update(post_subset)

        if not predicates:
            predicates = set(chain.from_iterable([list(x.keys()) for x in rendered]))
        predicate_labels = gs.get_labels(conn, list(predicates), statement=table_name)

        # Create the HTML output of data
        table_data = []
        for term_id, predicate_objects in data.items():
            # We always display the ID, regardless of other columns
            term_id = html_escape(term_id)
            term_data = {
                "ID": render(
                    [
                        "a",
                        {"href": url_for("cmi-pb.term", table_name=table_name, term_id=term_id)},
                        term_id,
                    ],
                )
            }
            for predicate, objs in predicate_objects.items():
                term_data[predicate_labels.get(predicate, predicate)] = objs
            table_data.append(term_data)
        if len(data) == 1:
            # Single term view
            predicates = table_data[0].keys()
            base_url = url_for("cmi-pb.term", table_name=table_name, term_id=list(data.keys())[0])
        else:
            base_url = url_for("cmi-pb.table", table_name=table_name)
        try:
            predicates = list(predicates)
            if "ID" not in predicates:
                predicates.insert(0, "ID")
            return render_html_table(
                table_data,
                table_name,
                request.args,
                base_url=base_url,
                columns=[predicate_labels.get(p, p) for p in predicates],
                ignore_params=["project-name", "branch-name", "view-path"],
                show_filters=False,
                standalone=False,
            )
        except SprocketError as e:
            abort(422, str(e))
    elif fmt.lower() in ["tsv", "csv"]:
        # Create TSV or CSV export of data
        field_sep = request.args.get("sep", "|")
        mt = "text/tab-separated-values"
        delimiter = "\t"
        if fmt.lower() == "csv":
            delimiter = ","
            mt = "text/comma-separated-values"
        data = terms2dicts(conn, data_subset, sep=field_sep, statement=table_name)
        return Response(dicts2tsv(data, data[0].keys(), delimiter=delimiter), mimetype=mt)
    else:
        return abort(400, "Unknown export format: " + fmt)


def render_subclass_of(table_name: str, param: str, arg: str) -> Optional[Response]:
    """Render an ontology table that includes the subclasses of a given term.

    :param table_name: ontology statement table
    :param param: name of query parameter (subClassOf, subClassOf?, subClassOfplus, subClassOf*)
    :param arg: value of query parameter (ontology term)
    :return: Response or HTML string
    """
    id_to_label = get_terms_from_arg(table_name, arg)

    terms = set()
    if param == "subClassOf":
        for p in id_to_label.keys():
            terms.update(gs.get_children(SQLITE_CONN, p, statement=table_name))
    elif param == "subClassOf?":
        terms.update(id_to_label.keys())
        for p in id_to_label.keys():
            terms.update(gs.get_children(SQLITE_CONN, p, statement=table_name))
    elif param == "subClassOfplus":
        for p in id_to_label.keys():
            terms.update(gs.get_descendants(SQLITE_CONN, p, statement=table_name))
    elif param == "subClassOf*":
        terms.update(id_to_label.keys())
        for p in id_to_label.keys():
            terms.update(gs.get_descendants(SQLITE_CONN, p, statement=table_name))
    else:
        abort(400, "Unknown 'subClassOf' query parameter: " + param)

    if request.args.get("format") == "json":
        # Support for searching the subset of these terms
        data = search(
            SQLITE_CONN,
            limit=30,
            search_text=request.args.get("text", ""),
            statement=table_name,
            term_ids=list(terms),
        )
        return json.dumps(data)
    # Maybe get a set of predicates to restrict search results to
    select = request.args.get("select")
    predicates = ["rdfs:label", OPTIONS["synonym"]]
    if select:
        # TODO: add form at top of page for user to select predicates to show?
        pred_labels = select.split(",")
        predicates = gs.get_ids(
            SQLITE_CONN, id_or_labels=pred_labels, id_type="predicate", statement=table_name
        )

    data = gs.get_objects(
        SQLITE_CONN, predicates, exclude_json=True, statement=table_name, term_ids=list(terms)
    )
    response = render_ontology_table(table_name, data, predicates=predicates)
    if isinstance(response, Response):
        return response

    hrefs = [
        f"<a href='/{url_for('cmi-pb.term', table_name=table_name, term_id=term_id)}'>{label}</a>"
        for term_id, label in id_to_label.items()
    ]
    return render_template(
        "template.html",
        add_params=f"{param}={arg}",
        base_ontology=OPTIONS["base_ontology"],
        html=response,
        import_table=OPTIONS["import_table"],
        ontologies=get_display_ontologies(),
        project_name=OPTIONS["title"],
        show_search=True,
        table_name=table_name,
        tables=get_display_tables(),
        title=get_ontology_title(conn, table_name),
        subtitle="Showing children of " + ", ".join(hrefs),
    )


def render_term_form(table_name: str, term_id: str) -> str:
    """Generate an editable form for a term from an ontology table. This currently is in use, but you cannot POST from
    the form. TODO: support LDTab

    :param table_name: name of ontology statement table
    :param term_id: term to generate a form for
    :return: HTML page with form
    """
    global FORM_ROW_ID
    entity_type = gs.get_top_entity_type(SQLITE_CONN, term_id, statement=table_name)

    # Get all annotation properties
    query = sql_text(
        f'SELECT DISTINCT predicate FROM "{table_name}" WHERE predicate NOT IN :logic',
    ).bindparams(bindparam("logic", expanding=True))
    results = SQLITE_CONN.execute(query, {"logic": LOGIC_PREDICATES}).fetchall()
    aps = gs.get_labels(SQLITE_CONN, [x["predicate"] for x in results], statement=table_name)

    predicates = gs.get_ids(SQLITE_CONN, id_type="predicate", statement=table_name)
    term_details = gs.get_objects(SQLITE_CONN, predicates, statement=table_name, term_ids=[term_id])
    if not term_details:
        return abort(400, f"Unable to find term {term_id} in '{table_name}' table")
    term_details = term_details[term_id]

    # Separate details into metadata & logic
    metadata = {k: v for k, v in term_details.items() if k not in LOGIC_PREDICATES}
    logic = {k: v for k, v in term_details.items() if k in LOGIC_PREDICATES}

    # Build the metadata form elements, starting with term ID (always displayed first)
    metadata_html = [
        get_hiccup_form_row(
            "ID", display_header="ontology ID", html_type="text", readonly=True, value=term_id
        )
    ]

    # Add the label element (always displayed second)
    label_details = term_details.get("rdfs:label")
    label = None
    if label_details:
        # TODO: handle multiple labels
        label_details = label_details[0]
        label_annotation = label_details.get("annotation")
        if label_annotation:
            label_annotation = json.loads(label_annotation)
        label = label_details.get("object")
        # TODO: get label label
        metadata_html.append(
            get_hiccup_form_row(
                "rdfs:label",
                annotations=label_annotation,
                display_header="label",
                html_type="text",
                value=label,
            )
        )

    # Add the rest of the annotations
    for predicate_id, detail in metadata.items():
        if predicate_id == "rdfs:label":
            continue
        # TODO: support other HTML types (dropdown, boolean, etc.)
        pred_label = aps.get(predicate_id, predicate_id)
        html_type = "text"
        if pred_label in ["definition", "comment", "rdfs:comment"]:
            html_type = "textarea"

        for d in detail:
            d_annotations = None
            if d.get("annotation"):
                d_annotations = json.loads(d.get("annotation"))
            metadata_html.append(
                get_hiccup_form_row(
                    predicate_id,
                    allow_delete=True,
                    annotations=d_annotations,
                    display_header=pred_label,
                    html_type=html_type,
                    value=d.get("object"),
                )
            )

    logic_html = []
    # TODO: use wiring to render the object
    for predicate_id, objects in logic.items():
        pred_label = BUILTIN_LABELS.get(predicate_id, aps.get(predicate_id, predicate_id))
        for o in objects:
            o_annotations = None
            if o.get("annotation"):
                o_annotations = json.loads(o.get("annotation"))
            logic_html.append(
                get_hiccup_form_row(
                    predicate_id,
                    allow_delete=True,
                    annotations=o_annotations,
                    display_header=pred_label,
                    html_type="search",
                    value=o.get("object"),
                )
            )

    if label and " " in label:
        # Encase in single quotes when label has a space
        label = f"'{label}'"

    metadata_html.insert(0, {"class": "row", "id": "term-metadata"})
    metadata_html.insert(0, "div")

    logic_html.insert(0, {"class": "row", "id": "term-logic"})
    logic_html.insert(0, "div")

    # Reset form row ID for next time
    FORM_ROW_ID = 0
    return render_template(
        "ontology_form.html",
        base_ontology=OPTIONS["base_ontology"],
        import_table=OPTIONS["import_table"],
        project_name=OPTIONS["title"],
        table_name=table_name,
        tables=get_display_tables(),
        ontologies=get_display_ontologies(),
        term_id=term_id,
        annotation_properties=aps,
        metadata=render(metadata_html),
        logic=render(logic_html),
        entity_type=entity_type,
        title=f"Update " + label or term_id,
    )


def render_tree(conn, table_name: str, term_id: str = None) -> str:
    """Generate the page for the tree view for an ontology statement table. If a term_id is not supplied, the default
    'Class' page will show with a help message.

    :param table_name: name of ontology statement table
    :param term_id: optional term_id to render tree view for
    :return: HTML page with tree view
    """
    if not is_ontology(conn, table_name):
        return abort(418, "Cannot show tree view for non-ontology table")

    # nothing to search, just return the tree view
    href = unquote(url_for("cmi-pb.term", table_name=table_name, view="tree", term_id="{curie}"))
    html = gadget_tree(
        conn,
        href=href,
        include_search=False,
        predicate_ids=OPTIONS["tree_predicates"],
        standalone=False,
        max_children=OPTIONS["max_children"],
        statement=table_name,
        term_id=term_id,
    )

    # Determine if we need to include add/edit buttons
    add_btn = None
    edit_btn = None
    if term_id and term_id not in gs.TOP_LEVELS:
        term_loc = get_term_location(term_id)
        if term_loc:
            edit_btn = {
                "text": "Edit term in " + term_loc,
                "url": url_for("cmi-pb.term", table_name=term_loc, term_id=term_id, view="form"),
            }
            if table_name == OPTIONS["base_ontology"] and term_loc != OPTIONS["import_table"]:
                # Always include an add button which adds a new term in same template
                add_btn = {
                    "text": "New term in " + term_loc,
                    "url": url_for("cmi-pb.table", table_name=term_loc, view="form"),
                }
        elif table_name != OPTIONS["base_ontology"] and OPTIONS["import_table"]:
            # Only include add button if its not already in import
            term_labels = gs.get_labels(conn, [term_id], statement=table_name)
            if term_labels:
                term_label = term_labels[term_id]
                url_args = {
                    "table_name": OPTIONS["import_table"],
                    "view": "form",
                    "Source": table_name,
                    "ID": term_id,
                    "Label": term_label,
                }
                add_btn = {
                    "text": "Add to " + OPTIONS["base_ontology"],
                    "url": url_for("cmi-pb.table", **url_args),
                }

    return render_template(
        "template.html",
        add_btn=add_btn,
        base_ontology=OPTIONS["base_ontology"],
        edit_btn=edit_btn,
        html=html,
        import_table=OPTIONS["import_table"],
        ontologies=get_display_ontologies(),
        project_name=OPTIONS["title"],
        show_search=True,
        table_name=table_name,
        tables=get_display_tables(),
        title=get_ontology_title(conn, table_name, table_active=False, term_id=term_id),
    )


def run(
    db,
    table_config,
    postgres_url=None,
    base_ontology=None,
    cgi_path=None,
    default_params=None,
    default_table=None,
    flask_host="127.0.0.1",
    flask_port=5000,
    hide_index=False,
    import_table=None,
    log_file=None,
    max_children: int = 20,
    synonym: str = "IAO:0000118",
    title: str = "Terminology",
    tree_predicates: list = None,
):
    """Run nanobot with supplied options.

    :param db: path to database
    :param table_config: path to table TSV file
    :param base_ontology: the name of the LDTab table for the base ontology of this project
    :param cgi_path: path to the script to use as SCRIPT_NAME environment variable
                     - this will run the app in CGI mode
    :param default_params: the query parameters to use for the default_table redirection
    :param default_table: the name of the table to redirect to from index (if None, will show index)
    :param flask_host: host to run the Flask app on
    :param flask_port: port to run the Flask app on
    :param hide_index: if True, hide the table of type index
    :param import_table: name of the ontology import table - this table must have the import module
                         columns specified by https://github.com/ontodev/gadget
    :param log_file: path to a log file - if not provided, logging will output to console
    :param max_children: max number of child nodes to display in tree view
    :param synonym: ID for the annotation property to use as synonym in search table (IAO:0000118)
    :param title: project title to display in header
    :param tree_predicates: ordered list of predicates to display in tree browser - all remaining
                            predicates can be displayed in alphabetical order after the sorted
                            predicates using '*'
    """
    global CONFIG, PG_CONN, SQLITE_CONN, LOGGER, OPTIONS

    # Override default options
    for k in OPTIONS.keys():
        v = locals().get(k)
        if v:
            OPTIONS[k] = v

    app = Flask(__name__)
    app.register_blueprint(BLUEPRINT)
    app.url_map.strict_slashes = False

    # Set up logging to file
    LOGGER = logging.getLogger("cmi_pb_logger")
    LOGGER.setLevel(logging.DEBUG)
    if log_file:
        fh = logging.FileHandler(log_file)
        fh.setLevel(logging.DEBUG)
        fh.setFormatter(
            logging.Formatter("%(asctime)s - %(levelname)s: %(message)s", "%Y-%m-%d %H:%M:%S")
        )
        LOGGER.addHandler(fh)

    CONFIG = configure_and_or_load(table_config, db, False)
    CONFIG = json.loads(CONFIG)
    CONFIG["db"] = db

    # SQLAlchemy connection required for sprocket/gizmos
    abspath = os.path.abspath(db)
    sqlite_url = "sqlite:///" + abspath + "?check_same_thread=False"
    #print(f"******************* {sqlite_url} *****************")
    sqlite_engine = create_engine(sqlite_url)
    SQLITE_CONN = sqlite_engine.connect()
    #res = SQLITE_CONN.execute('SELECT * from "assay"').fetchone()
    #print(f"******************* {res} *******************")

    if postgres_url:
        pg_engine = create_engine(postgres_url)
        PG_CONN = pg_engine.connect()
        #res = PG_CONN.execute('SELECT * from "assay"').fetchone()
        #print(f"******************* {res} *******************")

    if cgi_path:
        os.environ["SCRIPT_NAME"] = cgi_path
        from wsgiref.handlers import CGIHandler

        CGIHandler().run(app)
    else:
        LOGGER.error(os.path.abspath(os.path.join(os.path.dirname(__file__), "templates")))
        app.run(host=flask_host, port=flask_port)
