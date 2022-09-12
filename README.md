# nanobot

## Setup

`nanobot` requires Python version >=3.9. Ensure you have this installed, then set up a virtual environment and install `nanobot` and its dependencies.
```sh
$ python3.9 -m venv .venv
$ source .venv/bin/activate
# Within a virtual environment, `python` resolves to the version used to create it.
(.venv) $ python -m pip install -e .
# VALVE is currently only available vie TestPyPI
(.venv) $ pip install -i https://test.pypi.org/simple/ ontodev-valve
```

Finally, you will need to install `wiring.py` following the directions [here](https://github.com/ontodev/wiring.py)

## Database

`nanobot` requires a database created by VALVE's [configure_and_or_load](https://docs.rs/ontodev_valve/0.1.9/ontodev_valve/fn.configure_and_or_load.html) function. The python binding for this function is given by [ontodev_valve.py_configure_and_or_load](https://github.com/ontodev/valve.py/blob/eaca2ad08d8a5b8cca95750c2e1560221c946373/valve_py.rs#L19)

## Usage

To run the server, you'll need to write a small `run.py` script (or any name you'd like to use). This script should call `nanobot.run`. For example:
```python
#!/usr/bin/env python3.9
import os

from nanobot import run


if __name__ == '__main__':
    run(
        "my-database.db",     # path to database with tables
        "table.tsv",          # path to "table" table
        base_ontology="mro",  # name of base ontology for project
        title="MRO",          # project title to display in header
    )
```

### Run Options

The `run` function requires the database path and the table path, but also accepts the following optional parameters:
* `base_ontology`: the name of the LDTab table for the base ontology of this project
* `cgi_path`: path to the script to use as SCRIPT_NAME environment variable (setting this will run the app in CGI mode)
	* When running in CGI mode, make sure to change to the correct base directory of the database and table (e.g., `os.chdir("../..")`)
* `default_params`: the query parameters to use for the default_table redirection
* `default_table`: the name of the table to redirect to from base URL (if not specified, an index page will be generated)
* `hide_index`: if True, hide the table of type index
* `flask_host`: host to run the Flask app on (default: `127.0.0.1`, i.e. `localhost`)
* `flask_port`: port to run the Flask app on (default: `5000`)
* `import_table`: name of the import table for an ontology project - this table must have the headers needed for `gadget` [import modules](https://github.com/ontodev/gadget#creating-import-modules)
* `log_file`: path to a log file - if not provided, logging will output to console
* `max_children`: max number of child nodes to display in tree view
* `synonym`: predicate ID for the annotation property to use as synonym in search table (default is IAO:0000118)
* `title`: project title to display in header bar
* `tree_predicates`: list of predicate IDs in order that they should be displayed in the tree view - all remaining predicates should be specified with "\*"
