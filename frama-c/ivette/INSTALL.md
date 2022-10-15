# Dependencies

Required package to be installed:
- `yarn` for node pakage management;
- `pandoc` for generating the documentation;
- `node` version 16.x;

We recommand to use node v16 as a workaroung against incompatible versions of
SSL and Webpack packages. However, under Arch Linux, the standard node v17 is
also known to work.

## Linux

```sh
$ curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.34.0/install.sh | bash
$ nvm install 16
$ nvm use 16
$ npm install yarn
```

Under Arch you can simply rely on the `yarn` package and its `node` standard
dependency:

```sh
$ pacman -S yarn
```

## macOS

```sh
$ brew install yarn
$ brew install nvm # follow instructions
$ nvm install 16
$ nvm use 16
```

# Installation

You shall have configured `frama-c` before installing Ivette. Notice that, by
default, the installed `ivette` command will look for an installed `frama-c`
command to run the server.

From the `Frama-C` main directory, simply type:

```
$ autoconf -f
$ ./configure
$ make -C ivette dist
$ [sudo] make -C ivette install
```

If this is the first time you compile `ivette`, this might take some time to download
all the necessary packages and Electron binaries from the web.

The first `make` command builds a binary distribution of Ivette for your
architecture in `ivette/dist/<arch>` ; the second `make` command installs it on
your system accordingly.

The installed command is `<prefix>/bin/ivette` which is actually just a wrapper
to launch the Ivette application. The Ivette application itself is installed:

- **Linux:** in `<prefix>/lib/ivette/*`
- **macOS:** in `/Applications/Ivette.app`

# Developer Setup

Ivette can be compiled and used with different modes:

- `make dev` builds and start the development version with live-code-editing enabled. It uses
  local binaries of Electron framework. This is _not_ a full packaged
  application.

- `make app` pre-builds the production application. It is not _yet_ packaged and still
  uses the local Electron binaries.

- `make dist` packages the pre-built application into a new application for the host
  operating system, see Installation section above.

The development and production applications can be launched from the command
line with `Frama-C/ivette/bin/ivette` wrapper. The generated `ivette` script
will use the local `Frama-C/bin/frama-c` binary by default, although you can
change this behaviour by using `ivette` command-line options.

The `ivette` application and its installed or local wrappers accept the
following command line options:

```
ivette [ivette options] [frama-c command line]
  -R|--reload re-run the last command from history (other options are discarded)
  -C|--working <dir> change the working directory used by ivette & frama-c
  -B|--command <bin> set the frama-c server to be launched
  --socket <socket> set the Linux socket name to be used for the frama-c server
```

See also the [CONTRIBUTING] guide for editor configuration if you want to hack in Ivette
source code.
