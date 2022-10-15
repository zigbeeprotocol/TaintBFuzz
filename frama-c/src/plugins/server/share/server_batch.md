# Batch Protocol

This section presents a Frama-C command-line entry point to Server requests.
Although it is not full-featured server entry point, it allows for executing
requests from the command line or JSON scripts.

The `-server-script` option of the Frama-C/Server plug-in takes a (list of)
script file `<file.json>`, parse it and execute its commands, and output the
reponses in file `<file.out.json>`.

## Input Script Format

A JSON script is either a single JSON command or an array of JSON commands, or `null`.
Each command is a record with the following fields:

| Input Field | Format | Description |
|:------|:-------|:-----------:|
| `id` | _any_ ? | The command identifier (optional) |
| `request` | _string_ | The request name |
| `data` | _any_ | The request input parameters |

## Output Script Format

Each command leads to an assiated JSON record, with the following fields:

| Output Field | Format | Description |
|:------|:-------|:-----------:|
| `id` | _any_ ? | The command identifier (as provided in input) |
| `data` | _any_ ? | The request output parameters (if successfull) |
| `error` | _string_ ? | The request error message (in case of occurence) |
| `at` | _any_ ? | Wrongly encoded part of the request (when appropriate) |
