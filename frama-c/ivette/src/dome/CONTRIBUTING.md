## Authorship

All contributions are proprietary of CEA Tech.
An exhaustive list of authors is maintained in [CONTRIBUTORS.md] file.

## Git Conventions

The branches are organized as follows:

- `master` is the prototype for building the next release.
- `stable` is the current working candidate for the next release.
It shall be an ancestor of `master` and is considered ready to be distributed.
- `release/DOME-vN.N.N` are tags pointing to public releases of the framework.
- `feature/*` are branches where new development are experimented before being merged
into `master`.

The release branches `master`, `stable` and `release/*` are protected and only
release managers are authorized to merge into.

It is highly recommended to not rebase `feature` branches already pushed on the repository,
unless there is only one contributor to the feature, on order to avoid losing data.

## Javascript Coding Rules

Your favorite editor shall be configured such that:
- indentation in two-spaces per level, with no tabulation
- module names are lowercase identifiers
- react compomnents are capitalized

## Framework Organization

- [CHANGELOG.md] tracks modifications with releases
- [CONTRIBUTING.md] recommandations for Dome developpers
- [CONTRIBUTORS.md] maintains the list of authors
- [LICENSE.md] framework terms and conditions
- [README.md] public description
- `./Makefile` framework quick-testing
- `./doc` framework documentation resources
- `./dist` local build for tests (generated)
- `./html` local documentation (generated)
- `./src/dome` framework sources
- `./template` framework configuration templates

For developping an application with **Dome**, follow the indications
provided by the [README.md] file.

The root Makefile is _not_ designed for
developping an application with the **Dome** framework.
See `make` or `make help` for details.

This Makefile has been designed for live-editing and quick-testing the
framework itself (see « Live Editing » chapter of Html documentation).
You can type `make dev` to generate an application in `.` and live-edit the
generated `./src/main/*.js` and `./src/renderer/*.js` files.
Then, `make app` and `make dist` can be used to test the framework in production mode.
Use `make doc` to build the documentation in `./html` directory.
