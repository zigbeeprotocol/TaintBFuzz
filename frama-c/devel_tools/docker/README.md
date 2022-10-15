# Frama-C Docker images

Frama-C Docker images are currently based on Alpine Linux,
using opam's Docker images
(from https://hub.docker.com/r/ocaml/opam/).

The user is `opam` and it has sudo rights.
To add packages, run `sudo apk add <package>`.

## Using the Makefile

The `Makefile` contains several targets and templates to build most
Frama-C versions. For each version, there are three images: one
for the command-line version `frama-c`; a stripped-down version of the former,
for a slimmer image, but which does not allow recompilation of Frama-C
or of any external plugin; and a third image including the graphical
interface (`frama-c-gui`), to be used with Singularity, x11docker, or any other
tool which enables running a graphical application from a Docker image.

Run `make` to get a list of targets.

If you have access to the Frama-C Docker Hub, you can also run a
`push-<version>` target to upload images related to that version to
the Docker Hub.

## Commands to generate images

Some commands in this section are those used by the above Makefile;
others allow creating different images (e.g. with the Frama-C sources)
which are not directly available as Makefile targets.

Note: a Dockerfile is needed for the commands below.
      For most versions, running `make Dockerfile.dev` and then using it
      (adding `-f Dockerfile.dev` to the commands below) is enough.
      However, if specific build commands or dependencies are needed,
      you can copy the generated Dockerfile
      (e.g. `cp Dockerfile.dev Dockerfile`) and adapt it as needed,
      before running one of the commands below.

- Build slim development image (from public Git master branch):

        docker build . -t framac/frama-c:dev --target frama-c-slim

- Build slim development image with GUI:

        docker build . -t framac/frama-c-gui:dev --target frama-c-gui-slim

- Build stripped (minimal) version:

        docker build . -t framac/frama-c:dev-stripped --target frama-c-stripped

- Build image from archive (note: it _must_ be named `frama-c-<something>.tar.gz`, where
  `<something>` may be a version number, codename, etc:

        docker build . -t framac/frama-c:dev --target frama-c-slim --build-arg=from_archive=frama-c-<version>.tar.gz

- Build image containing Frama-C's source code in `/frama-c` (without and with GUI):

        docker build . -t framac/frama-c-source:dev --target frama-c
        docker build . -t framac/frama-c-gui-source:dev --target frama-c-gui

- Start Singularity instance

        singularity instance start docker-daemon:framac/frama-c-gui:dev <instance name>

- Run command with Singularity instance

        singularity exec instance://<instance name> <command with args>
