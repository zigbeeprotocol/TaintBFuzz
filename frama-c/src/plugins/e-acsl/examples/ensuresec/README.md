# Ensuresec

This folder illustrates the developments done for the European H2020 project
Ensuresec.

## Usage

The `Makefile` in the root folder provides targets to launch some tests.

- `compile`: Compile the example in folder `json-output`;
- `run`: Run the example in folder `json-output`;
- `launch_receiver`: Launch the test server in folder `push-alerts`;
- `run_wrapped`: Run the example in folder `json-output` wrapped with the script
  in folder `push-alerts`. The test server must be launched before executing
  this target.
- `run_wrapped_print_all`: Same than

When using `make run`, the alerts raised by the example are saved to a JSON file
in `./json-output/build/ensuresec_ee.json`.

To test pushing alerts to a web API, `make launch_receiver` should be run in a
secondary terminal. Then `make run_wrapped` can be executed in the primary
terminal and alerts raised by the example should be visible on the receiver. The
target `run_wrapped_print_all` will also push valid assertions.

## Files

### Folder `json-output`

Custom E-ACSL assert to output alerts in a JSON file.

#### `Makefile`

The makefile in the folder provides some targets to test the ensuresec
developments:

- `compile` (default): Compile `ensuresec_ee.c` with the external assert
  implementation in `json_assert.c`.
- `compile_print_all`: Same as `compile` but every assertion (valid or invalid)
  will be printed to the output.
- `compile_debug`: Same as `compile_print_all` but in debug mode.
- `run`: run the output of the `compile` step.
- `run_print_all`: run the output of the `compile_print_all` step.
- `run_debug`: run the output of the `compile_debug` step.

#### `json_assert.c`

The file `json_assert.c` contains an external `__e_acsl_assert()` implementation
that will print assertion violations to a json file.

The following environment variables must be defined when using this
implementation:

- `ENSURESEC_EE_ID`: Ensuresec e-commerce ecosystem id
- `ENSURESEC_EE_TOOL_ID`: Ensuresec e-commerce ecosystem tool id
- `ENSURESEC_OUTPUT_FILE`: json output file

#### `ensuresec_ee.c`

Multithread program serving as an exemple Ensuresec e-commerce ecosystem
program. The program contains `check` assertions that will be violated during
its execution without halting the program.

### Folder `push-alerts`

Example of wrapping script to push alerts emitted by the program in
`json-output` to a specific URL.

#### `wrapper.py`

Wrapper for an E-ACSL monitored executable that will `POST` each raised alert to
a specific URL. See `./wrapper.py -h` for how to use the script.

Python dependencies:

- `python-dotenv`
- `python-ijson`
- `python-requests`

#### `.env-example`

Example `.env` file with environment variables read by `wrapper.py`.

#### `receiver.py`

Test server that listen on URL `http://localhost:5000/alert` for JSON emitted by
an E-ACSL monitored program and print received alerts to the console output.

Run with `FLASK_APP=receiver.py FLASK_ENV=development flask run`

Python dependencies:

- `python-flask`
