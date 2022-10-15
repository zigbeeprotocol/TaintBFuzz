# Dome Framework

This project allows you to build and distribute desktop applications.
The proposed framework is based on **React** [1] and **Electron** [2].

## Quick Start

We strongly recommand to use **Yarn** [3] for installing the
necessary **Node** packages and their dependencies. Both shall be installed
with decently recent versions (`yarn -v 1.5.*` and `node -v 8.*`).

Then, prepare a directory for developing your application, and download
the Dome Application Framework into sub-directory `dome`.
You shall setup a makefile for your application as follows:

```
include dome/template/makefile
all: dome-dev
```

Now, simply type `make` and all the necessary packages will be automatically
installed and configured. This can take a while for the very first installation.
Eventually, your application shall start with a « _Hello World_ » window.  Now,
simply live edit the generated `src/renderer/Application.js` which is the main
entry point of your application.

## Advanced Usage

You may install the framework in any directory,
provided you set the `DOME` makefile or environment variable accordingly.
By default, this variable is set to `./dome` by the template makefile.

Type `make help` to see all the predefined compilation targets.
In particular, `make dome-doc` will generate the Dome Documentation locally, in
`$(DOME)/html/index.hml`.

The `$(DOME)/template/makefile` is provided with usefull targets, but you can also
use your own scripts. All generated configuration files are borrowed from
resources located in the `$(DOME)/template` directory. You can extend and modify
all the generated files, simply follow the comments provided.

Typicall installation places for the Dome framework are:
- `DOME=./dome` for usual application developpers;
- `DOME=./src/dome` for application developpers that also have to hack and live-edit the Dome framework;
- `DOME=.` is also possible to quick test the framework or make a demo in `src/renderer/Application.js`.

The last option is not possible when installing the framework since it would conflict with your
own project development. For instance, if your install Dome with `git`, you must keep the `$(DOME)/.git`
distinct and ignore the entire `$(DOME)` directory in your own versionned files.

## References

[1] https://reactjs.org

[2] https://electronjs.org

[3] https://yarnpkg.com/lang/en/docs/install/
