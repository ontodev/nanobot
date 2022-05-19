# nanobot

## Setup

`nanobot` requires Python version >=3.9. Ensure you have this installed, then set up a virtual environment and install `nanobot` and its dependencies:
```
$ python3 -m venv .venv
$ source .venv/bin/activate
$ python3 -m pip install -e .
```

Finally, you will need to install `wiring.py` following the directions [here](https://github.com/ontodev/wiring.py)

## Database

TODO: `nanobot` requires a database created by `cmi_pb_script.load`

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
* `log_file`: path to a log file - if not provided, logging will output to console
* `max_children`: max number of child nodes to display in tree view
* `synonym`: predicate ID for the annotation property to use as synonym in search table (default is IAO:0000118)
* `title`: project title to display in header bar
