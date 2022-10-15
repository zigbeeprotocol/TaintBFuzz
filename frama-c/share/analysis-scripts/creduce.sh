#!/bin/bash -e
##########################################################################
#                                                                        #
#  This file is part of Frama-C.                                         #
#                                                                        #
#  Copyright (C) 2007-2022                                               #
#    CEA (Commissariat à l'énergie atomique et aux énergies              #
#         alternatives)                                                  #
#                                                                        #
#  you can redistribute it and/or modify it under the terms of the GNU   #
#  Lesser General Public License as published by the Free Software       #
#  Foundation, version 2.1.                                              #
#                                                                        #
#  It is distributed in the hope that it will be useful,                 #
#  but WITHOUT ANY WARRANTY; without even the implied warranty of        #
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         #
#  GNU Lesser General Public License for more details.                   #
#                                                                        #
#  See the GNU Lesser General Public License version 2.1                 #
#  for more details (enclosed in the file licenses/LGPLv2.1).            #
#                                                                        #
##########################################################################

usage="
Script to run C-Reduce (https://embed.cs.utah.edu/creduce) when debugging
Frama-C, or when minimizing test cases resulting in a Frama-C error.

NOTE: some distributions now use 'cvise' (a Python port of creduce)
      instead of 'creduce', but it is backwards-compatible.

# Requirements

- C-Reduce installed in the PATH, or its path in environment variable CREDUCE;
- Frama-C installed in the PATH, or the path to its 'bin' directory in
   environment variable FRAMAC_BIN;
- a source file + a command line which causes Frama-C to crash with
  a 'fatal' error (producing a stack trace); can also be used when
  Frama-C reports other errors, but in this case a separate script must be
  completed by the user.

# Basic usage

  arguments: <script options> <file> <Frama-C command line options>

This script creates a temporary directory named 'creducing'. It copies <file>
inside it, then runs creduce with 'frama-c <command line options>'
on the copied file, modifying it to make it smaller while still crashing.

When done, you need to copy the reduced file and erase directory 'creducing'.

# Script options

Note: these options must be placed _before_ all other arguments.

--help: show this help message.

--ignore-parsability: do not check that each reduced program conforms to
                      a gcc parsability check; helps avoid issues due to
                      preprocessing flags.

# Advanced usage

- if <file> is not a preprocessed (.i) source, this script
  will retrieve the preprocessing arguments from Frama-C. It will try to
  preprocess the file in GCC to make sure it is parseable during reduction.
  This may cause some issues; use a preprocessed file if you can.

- For 'fatal' crashes (with stack trace and 'Please report...' message),
  this script should work automatically. For other crashes (e.g. invalid
  input), this script will copy a template to the current directory and you
  need to fill it so that creduce will work. This usage mode requires knowing
  how C-Reduce works.
"

#### Command-line and environment validation
#
#

ignore_parsability=0
while [ $# -ge 1 ]; do
    case "$1" in
        --help) echo "$usage"; exit;;
        --h) echo "$usage"; exit;;
        -help) echo "$usage"; exit;;
        -h) echo "$usage"; exit;;
        --ignore-parsability)
            ignore_parsability=1
            shift
            ;;
        *) break;;
    esac
done

if [ $# -lt 1 ]; then
    echo "$usage"
    exit
fi

file="$1"
base=$(basename "$file")
shift

dir_for_reduction="creducing"

script_for_creduce="./script_for_creduce.sh"

if [ -z "$CREDUCE" ]; then
    # Now some distributions have 'cvise' instead of 'creduce', so try it
    # if found in PATH
    if command -v cvise 2>&1 >/dev/null; then
        CREDUCE="cvise"
    else
        CREDUCE="creduce"
    fi
fi

if ! command -v "$CREDUCE" 2>&1 >/dev/null; then
    echo "cvise/creduce not found; install it in the PATH or"
    echo "put it in environment variable CREDUCE."
    exit 1
fi

if [[ ! -f "$file" ]]; then
    echo "Source file not found (must be first argument): $file"
    exit 1
fi

too_many_sources=""
for f in "$@"; do
    if [ -e "$f" ]; then
        too_many_sources+=" $f"
    fi
done
if [ ! -z "$too_many_sources" ]; then
    echo "error: too many sources; only the first argument must be a file: $file"
    echo "       remove these from the command-line:$too_many_sources"
    exit 1
fi

if [[ $(dirname "$file") = "$dir_for_reduction" ]]; then
    echo "error: cannot reduce a file inside the directory used for reduction,"
    echo "       $dir_for_reduction"
    exit 1
fi

if [ -z "$FRAMAC_BIN" ]; then
    if ! command -v "frama-c" >/dev/null; then
        echo "error: frama-c must be in the PATH, or FRAMAC_BIN must point to"
        echo "       the directory containing the frama-c binary"
        exit 1
    fi
    FRAMAC="frama-c"
else
    FRAMAC="$FRAMAC_BIN/frama-c"
fi
echo "[info] using FRAMAC: $FRAMAC"

if [ -z "$FRAMAC_SHARE" ]; then
    FRAMAC_SHARE="$("$FRAMAC" -print-share-path)"
fi

if ! sed --version >/dev/null 2>&1; then
    echo "[info] sed is not GNU, trying gsed..."
    if command -v gsed >/dev/null; then
        echo "[info] gsed found, using it."
        SED="gsed"
    else
        echo "error: GNU sed is required but was not found (neither sed nor gsed)"
        exit 1
    fi
else
    SED="sed"
fi

#
#
#### End of command-line and environment validation

if [[ ! "$options" =~ no-autoload-plugins ]]; then
    echo "********************************************************************"
    echo "Hint: consider using -no-autoload-plugins -load-module [modules]"
    echo "      for faster reduction"
    echo "********************************************************************"
fi

if [[ "$base" =~ \.c$ ]]; then
    echo "********************************************************************"
    echo "Hint: consider passing a preprocessed (.i) file if possible,"
    echo "      otherwise #includes may prevent further reduction"
    echo "********************************************************************"
    # TODO: check for libc includes and suggest -print-libc
fi

# Obtain cpp flags by running Frama-C with `-kernel-msg-key pp`
if [[ "$base" =~ \.i$ ]]; then
    # Preprocessed file: no need to get preprocessing flags
    # TODO: check for '-machdep' option and add/remove flags accordingly
    CPP="gcc -fsyntax-only"
else
    set +e
    cpp_output=$("$FRAMAC" -print-cpp-commands "$@" "$file" 2>/dev/null)
    cpp_retcode=$?
    set -e
    if [ $cpp_retcode -ne 0 ]; then
        echo "error trying to get preprocessing flags (exit code: $cpp_retcode): $FRAMAC -print-cpp-commands $@ $file"
        exit $cpp_retcode
    fi
    CPP=$(echo "$cpp_output" | \
          "$SED" -n '/Preprocessing command:/{n;p;}' | "$SED" "s|'.*' -o '.*'||")
    if [[ "$CPP" = "" ]]; then
        echo "[info] Could not get preprocessing flags when running Frama-C,"
        echo "       using default flags"
        # TODO: check for '-machdep' option and add/remove flags accordingly
        CPP="gcc -fsyntax-only -m32"
    else
        # Replace -E with -fsyntax-only to force GCC to try parsing the file;
        # also remove Frama-C's libc; use the standard system libraries.
        CPP=$(echo $CPP | \
                  "$SED" 's| -E | -fsyntax-only |' | \
                  "$SED" 's| -nostdinc | |' | \
                  "$SED" 's| -I[^ ]\+/libc | |' )
    fi
fi

if [ ! -e "$script_for_creduce" ]; then
    echo "[info] $script_for_creduce not found."
    echo "Which kind of error are you reducing for?"
    echo "1. Fatal crash (error message with stacktrace)"
    echo "2. Non-fatal error"
    read -p "Please enter 1 or 2: " errorkind
    case $errorkind in
        1)
            cp "$FRAMAC_SHARE/analysis-scripts/script_for_creduce_fatal.sh" "$script_for_creduce"
            ;;
        2)
            cp "$FRAMAC_SHARE/analysis-scripts/script_for_creduce_non_fatal.sh" "$script_for_creduce"
            echo "Script copied. Please edit $script_for_creduce and re-run this script."
            exit 0
            ;;
        *)
            echo "Invalid choice, aborting."
            exit 0
            ;;
    esac
fi

if [ "$ignore_parsability" -eq 0 ]; then
    echo "[info] the following command will be used to check for syntactic validity during reduction:"
    echo "    $CPP"
fi

mkdir -p "$dir_for_reduction"
cp "$file" "$dir_for_reduction"
cp "$script_for_creduce" "$dir_for_reduction"
cd "$dir_for_reduction"

if [ "$ignore_parsability" -eq 0 ]; then
    "$SED" -i "s|@CPP@|$CPP|g" "$script_for_creduce"
else
    "$SED" -i "s|^.*@CPP@.*$||g" "$script_for_creduce"
fi
"$SED" -i "s|@FRAMAC@|$FRAMAC|g" "$script_for_creduce"
"$SED" -i "s|@BASE@|$base|g" "$script_for_creduce"
"$SED" -i "s|@FCFLAGS@|$(echo $@ | tr "'" "\\'")|g" "$script_for_creduce"
chmod u+x "$script_for_creduce"

trap '{ echo "Creduce interrupted!"; echo ""; echo "(partially) reduced file: $dir_for_reduction/$base"; exit 0; }' SIGINT

echo ""
echo "File being reduced: $dir_for_reduction/$base (press Ctrl+C to stop at any time)"

set +e
rm -rf /tmp/script_for_creduce.out
$script_for_creduce >>/tmp/script_for_creduce.out 2>&1
if [ $? -ne 0 ]; then
    # TODO: check if -cpp-extra-args exists and contains relative paths,
    # and if so, warn about them
    echo "#################################################"
    echo "ERROR: script did not produce the expected error."
    echo "       check the options given to Frama-C."
    echo "       If you edited '$script_for_creduce', check it as well."
    echo ""
    if [ $(wc -l /tmp/script_for_creduce.out | cut -d' ' -f1) -gt 20 ]; then
        echo "# Script output (first 20 lines):"
        head -n 20 /tmp/script_for_creduce.out
        echo "(...) [truncated; full output in /tmp/script_for_creduce.out]"
    else
        echo "# Script output:"
        cat /tmp/script_for_creduce.out
    fi
    exit 1
fi
set -e

"$CREDUCE" script_for_creduce.sh "$base"

echo "Finished reducing file: $dir_for_reduction/$base"
echo "Remember to remove 'script_for_creduce.sh' after you are done."
