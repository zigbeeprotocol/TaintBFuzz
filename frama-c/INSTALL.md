# Installing Frama-C

- [Installing Frama-C](#installing-frama-c)
    - [Table of Contents](#table-of-contents)
    - [Installing Frama-C via opam](#installing-frama-c-via-opam)
        - [Installing opam](#installing-opam)
        - [Installing Frama-C from opam repository](#installing-frama-c-from-opam-repository)
        - [Installing Custom Versions of Frama-C](#installing-custom-versions-of-frama-c)
        - [Installing Frama-C on Windows via WSL](#installing-frama-c-on-windows-via-wsl)
        - [Installing Frama-C on macOS](#installing-frama-c-on-macos)
    - [Installing Frama-C via your Linux distribution (Debian/Ubuntu/Fedora)](#installing-frama-c-via-your-linux-distribution-debianubuntufedora)
    - [Compiling from source](#compiling-from-source)
        - [Quick Start](#quick-start)
        - [Full Compilation Guide](#full-compilation-guide)
- [Testing the Installation](#testing-the-installation)
    - [Available resources](#available-resources)
        - [Executables: (in `/INSTALL_DIR/bin`)](#executables-in-install_dirbin)
        - [Shared files: (in `/INSTALL_DIR/share/frama-c` and subdirectories)](#shared-files-in-install_dirshareframa-c-and-subdirectories)
        - [Documentation files: (in `/INSTALL_DIR/share/frama-c/doc`)](#documentation-files-in-install_dirshareframa-cdoc)
        - [Object files: (in `/INSTALL_DIR/lib/frama-c`)](#object-files-in-install_dirlibframa-c)
        - [Plugin files: (in `/INSTALL_DIR/lib/frama-c/plugins`)](#plugin-files-in-install_dirlibframa-cplugins)
        - [Man files: (in `/INSTALL_DIR/share/man/man1`)](#man-files-in-install_dirsharemanman1)
- [Installing Additional Frama-C Plugins](#installing-additional-frama-c-plugins)
    - [HAVE FUN WITH FRAMA-C!](#have-fun-with-frama-c)

## Installing Frama-C via opam

[opam](http://opam.ocaml.org/) is the OCaml package manager. Every Frama-C
release is made available via an opam package.

First you need to install opam, then you may install Frama-C using opam.

### Installing opam

Several Linux distributions already include an `opam` package.

macOS has opam through Homebrew.

Windows users can install opam via WSL (Windows Subsystem for Linux).

If your system does not have an opam package >= 2, you can use the provided
opam binaries available at:

http://opam.ocaml.org/doc/Install.html

### Installing Frama-C from opam repository

The Frama-C package in opam is called `frama-c`, which includes both the
command-line `frama-c` executable and the graphical interface `frama-c-gui`.

`frama-c` has some non-OCaml dependencies, such as Gtk and GMP. On most
systems, `opam`'s `depext` mechanism can take care of installing these
external dependencies. As of version
2.1.0, `depext` is [directly included](https://opam.ocaml.org/blog/opam-2-1-0/#Seamless-integration-of-System-dependencies-handling-a-k-a-quot-depexts-quot)
in `opam`, so that the following command should install everything, at
least if your OS is supported by `depext` (and you have administrative
rights):

    opam install frama-c

For older `opam` versions, you have to install it
separately and call it explicitely with the following commands, before
installing Frama-C as above. Again, installing the external dependencies
requires administrative rights.

    # install Frama-C's dependencies with pre-2.1.0 opam
    opam install depext
    opam depext frama-c

If there are errors due to missing external dependencies, opam may emit a
message indicating which packages to install. If this is not sufficient,
there may be missing dependencies in opam's `depext` tool. In this case,
you may [create a Gitlab issue](https://git.frama-c.com/pub/frama-c/issues/new)
indicating your distribution and error message.

### Configuring provers for Frama-C/WP

Frama-C/WP uses the [Why3](http://why3.lri.fr/) platform to run external provers
for proving ACSL annotations.
The Why3 platform and the Alt-Ergo prover are automatically installed _via_ opam
when installing Frama-C.

Other recommended, efficient provers are CVC4 and Z3.
They can be used as replacement or combined with Alt-Ergo.
Actually, you can use any prover supported by Why3 in combination with Frama-C/WP.

Most provers are available on all platforms. After their installation,
Why3 must be configured to make them available for Frama-C/WP:

```shell
why3 config detect
```

### Reference configuration

See file [reference-configuration.md](reference-configuration.md)
for a set of packages that is known to work with Frama-C 24 (Chromium).

### Installing Custom Versions of Frama-C

If you have a **non-standard** version of Frama-C available
(with proprietary extensions, custom plugins, etc.),
you can use opam to install Frama-C's dependencies and compile your
own sources directly:

    # optional: remove the standard frama-c package if it was installed
    opam remove --force frama-c

    # install Frama-C's dependencies
    opam install depext # only for opam < 2.1.0
    opam depext frama-c # only for opam < 2.1.0
    opam install --deps-only frama-c

    # install custom version of frama-c
    opam pin add --kind=path frama-c <dir>

where `<dir>` is the root of your unpacked Frama-C archive.
See `opam pin` for more details.

If your extensions require other libraries than the ones already used
by Frama-C, they must of course be installed as well.

### Installing Frama-C on Windows via WSL

Frama-C is developed on Linux, but it can be installed on Windows using the
Windows Subsystem for Linux (WSL).

**Note**: if you have WSL2 (Windows 11), you can run the graphical interface
          directly, thanks to WSLg. If you are using WSL 1, you need to install
          an X server for Windows, such as VcXsrv
          (see section "Running the Frama-C GUI on WSL").

#### Prerequisites: WSL + a Linux distribution

To enable WSL on Windows, you may follow these instructions
(we tested with Ubuntu 20.04 LTS;
other distributions/versions should also work,
but the instructions below may require some modifications).

https://docs.microsoft.com/en-us/windows/wsl/install

Notes:

- older builds of Windows 10 and systems without access to the
  Microsoft Store may have no compatible Linux packages.
- in WSL 1, Frama-C/WP cannot use Why3 because of some missing features in WSL
  support, thus using WSL 2 is **highly recommended**.

#### Installing opam and Frama-C on WSL

To install opam, some packages are required. The following commands can be
run to update the system and install those packages:

```
sudo apt update
sudo apt upgrade
sudo apt install make m4 gcc opam gnome-icon-theme
```

Then opam can be set up using these commands:

```
opam init --disable-sandboxing --shell-setup
eval $(opam env)
opam install -y depext
```

You can force a particular Ocaml version during `opam init` by using the option
`-c <version>` if needed. For instance, you can try installing the OCaml version
mentioned in the [reference configuration](reference-configuration.md).

Now, to install Frama-C, run the following commands, which will use `apt` to
install the dependencies of the opam packages and then install them:

```
opam depext --install -y lablgtk3 lablgtk3-sourceview3
opam depext --install -y frama-c
```

#### Running the Frama-C GUI on WSL

If you have WSL2: a known issue with Frama-C 24.0 (Chromium), lablgtk3 and
Wayland require prefixing the command running the Frama-C GUI with
`GDK_BACKEND=x11`, as in:

    GDK_BACKEND=x11 frama-c-gui <options>

If you have WSL 1: WSL 1 does not support graphical user interfaces directly.
If you want to run Frama-C's GUI, you need to install an X server,
such as VcXsrv or Cygwin/X. We present below how to install VcXsrv.

First, install VcXsrv from:

https://sourceforge.net/projects/vcxsrv/

The default installation settings should work.

Now run VcXsrv from the Windows menu (it is named XLaunch), the firewall
must authorize both "Public" and "Private" domains. On the first configuration
screen, select "Multiple Windows". On the second:

- keep "Start no client" selected,
- keep "Native opengl" selected,
- select "Disable access control".

Now specific settings must be provided in WSL. you can put the export commands
in your `~/.bashrc` file, so this is done automatically when starting WSL.

##### WSL 1

The Xserver is ready. From WSL, run:

```
export LIBGL_ALWAYS_INDIRECT=1
export DISPLAY=:0
frama-c-gui
```

##### WSL 2

```
export LIBGL_ALWAYS_INDIRECT=1
export DISPLAY=$(cat /etc/resolv.conf | grep nameserver | awk '{print $2; exit;}'):0.0
frama-c-gui
```

### Installing Frama-C on macOS

[opam](https://opam.ocaml.org) works perfectly on macOS via
[Homebrew](https://brew.sh).
We highly recommend to rely on it for the installation of Frama-C.

1. Install *required* general macOS tools for OCaml:

    ```shell
    brew install autoconf pkg-config opam
    ```

   Do not forget to `opam init` and ``eval `opam config env` `` for a proper
   opam installation (if not already done before).

2. Set up a compatible OCaml version (replace `<version>` with the version
   indicated in the 'recommended working configuration' section):

    ```shell
    opam switch create <version>
    ```

3. Install *required* dependencies for Frama-C:

    ```shell
    brew install gmp gtk+ gtksourceview libgnomecanvas
    ```

    The graphical libraries require additional manual configuration of your
    bash profile. Consult this [issue](https://github.com/ocaml/opam-repository/issues/13709) on opam
    for details. A known working configuration is:

    ```shell
    export PKG_CONFIG_PATH=/usr/local/opt/libffi/lib/pkgconfig:/usr/local/opt/libxml2/lib/pkgconfig:/usr/local/lib/pkgconfig
    ```

4. Install *recommended* dependencies for Frama-C:

    ```shell
    brew install graphviz
    ```

5. Install Frama-C:

    ```shell
    opam install frama-c
    ```

## Installing Frama-C via your Linux distribution (Debian/Ubuntu/Fedora)

**NOTE**: Distribution packages are updated later than opam packages,
          so if you want access to the most recent versions of Frama-C,
          opam is currently the recommended approach.

Also note that it is **not** recommended to mix OCaml packages installed by
your distribution with packages installed via opam. When using opam,
we recommend uninstalling all `ocaml-*` packages from your distribution, and
then installing, exclusively via opam, an OCaml compiler and all the OCaml
packages you need. This ensures that only those versions will be in the PATH.

The advantage of using distribution packages is that dependencies are almost
always handled by the distribution's package manager. The disadvantage is that,
if you need some optional OCaml package that has not been packaged in your
distribution (e.g. `landmarks`, which is distributed via opam), it may be very
hard to install it, since mixing opam and non-opam packages often fails
(and is **strongly** discouraged).

Debian/Ubuntu: `apt-get install frama-c`

Fedora: `dnf install frama-c`

Arch Linux: `pikaur -S frama-c`

## Compiling from source

**Note**: These instructions are no longer required in the vast majority
          of cases. They are kept here mostly for historical reference.

### Quick Start

1. Install [opam](http://opam.ocaml.org/) and use it to get all of Frama-C's
   dependencies (including some external ones):

        opam install depext # only for opam < 2.1.0
        opam depext frama-c # only for opam < 2.1.0
        opam install --deps-only frama-c

   If not using [opam](http://opam.ocaml.org/), you will need to install
   the Frama-C dependencies by yourself. The `opam/opam` file in the Frama-C
   .tar.gz lists the required dependencies (e.g. `ocamlfind`, `ocamlgraph`,
   `zarith`, etc.). A few of these dependencies are optional, only required
   for the graphical interface: `lablgtk`, `conf-gnomecanvas` and
   `conf-gtksourceview` (or the equivalent Gtk+3 packages).

2. On Linux-like distributions:

        ./configure && make && sudo make install

    See section *Configuration* below for options.

3. On Windows+Cygwin:

        ./configure --prefix="$(cygpath -a -m <installation path>)" && make && make install

4. The binary `frama-c` (and `frama-c-gui` if you have lablgtk2) is now installed.

### Full Compilation Guide

#### Frama-C Requirements

See the `opam/opam` file, section `depends`, for compatible OCaml versions and
required dependencies (except for those related to `lablgtk`, which are
required for the GUI but otherwise optional).

Section `depopts` lists optional dependencies.

#### Configuration

Frama-C is configured by `./configure [options]`.

`configure` is generated by `autoconf`, so that the standard options for setting
installation directories are available, in particular `--prefix=/path`.

A plugin can be enabled by `--enable-plugin` and disabled by `--disable-plugin`.
By default, all distributed plugins are enabled, unless some optional
dependencies are not met.

See `./configure --help` for the current list of plugins, and available options.

##### Under Cygwin

Use `./configure --prefix="$(cygpath -a -m <installation path>)"`.

(using Unix-style paths without the drive letter will probably not work)


#### Compilation

Type `make` (you can use `-j` for parallelization).

Some Makefile targets of interest are:
- `doc`      generates the API documentation.
- `oracles`  sets up the Frama-C test suite oracles for your own configuration.
- `tests`    performs Frama-C's own tests.


#### Installation

Type `make install`
(depending on the installation directory, this may require superuser
privileges. The installation directory is chosen through `--prefix`).


#### API Documentation

For plugin developers, the API documentation of the Frama-C kernel and
distributed plugins is available in the file `frama-c-api.tar.gz`, after running
`make doc-distrib`.


#### Uninstallation

Type `make uninstall` to remove Frama-C and all the installed plugins.
(Depending on the installation directory, this may require superuser
privileges.)


# Testing the Installation

This step is optional.

Download some test files:

    export PREFIX_URL="https://git.frama-c.com/pub/frama-c/raw/master/tests/value"
    wget -P test ${PREFIX_URL}/CruiseControl.c
    wget -P test ${PREFIX_URL}/CruiseControl_const.c
    wget -P test ${PREFIX_URL}/CruiseControl.h
    wget -P test ${PREFIX_URL}/CruiseControl_extern.h
    wget -P test ${PREFIX_URL}/scade_types.h
    wget -P test ${PREFIX_URL}/config_types.h
    wget -P test ${PREFIX_URL}/definitions.h

Then test your installation by running:

    frama-c -eva test/CruiseControl*.c
    # or (if frama-c-gui is available)
    frama-c-gui -eva test/CruiseControl*.c

# Available resources

Once Frama-C is installed, the following resources should be installed and
available:

## Executables: (in `/INSTALL_DIR/bin`)

- `frama-c`
- `frama-c-gui`       if available
- `frama-c-config`    lightweight wrapper used to display configuration paths
- `frama-c.byte`      bytecode version of frama-c
- `frama-c-gui.byte`  bytecode version of frama-c-gui, if available
- `ptests.opt`        testing tool for Frama-c
- `frama-c-script`    utilities related to analysis parametrization

## Shared files: (in `/INSTALL_DIR/share/frama-c` and subdirectories)

- some `.h` and `.c` files used as preludes by Frama-C
- some `Makefiles` used to compile dynamic plugins
- some `.rc` files used to configure Frama-C
- some image files used by the Frama-C GUI
- some files for Frama-C/plug-in development (autocomplete scripts,
  Emacs settings, scripts for running Eva, ...)
- an annotated C standard library (with ACSL annotations) in `libc`
- plugin-specific files (in directories `wp`, `e-acsl`, etc.)

## Documentation files: (in `/INSTALL_DIR/share/frama-c/doc`)

- files used to generate dynamic plugin documentation

## Object files: (in `/INSTALL_DIR/lib/frama-c`)

- object files used to compile dynamic plugins

## Plugin files: (in `/INSTALL_DIR/lib/frama-c/plugins`)

- object files of available dynamic plugins

## Man files: (in `/INSTALL_DIR/share/man/man1`)

- `man` files for `frama-c` (and `frama-c-gui` if available)


# Installing Additional Frama-C Plugins

Plugins may be released independently of Frama-C.

The standard way for installing them should be:

    ./configure && make && make install

Plugins may have their own custom installation procedures.
Consult their specific documentation for details.


# HAVE FUN WITH FRAMA-C!
