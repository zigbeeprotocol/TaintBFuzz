#!/bin/bash -e

# Script to reduce a Frama-C crashing test case.

# This script requires no modification.
# Names between '@'s will be replaced by creduce.sh.

set +e
"@FRAMAC@" "@BASE@" @FCFLAGS@
retcode=$?
# see cmdline.ml for the different exit codes returned by Frama-C
if [ $retcode -eq 125 -o $retcode -eq 4 ]; then
    exit 0
else
    exit 1
fi
set -e
