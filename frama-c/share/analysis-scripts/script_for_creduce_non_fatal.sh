#!/bin/bash -e

# Script to reduce a Frama-C non-crashing test case.

# This script must be completed by the user.
# Names between '@'s will be replaced by creduce.sh.
# See the Frama-C User Manual for more details.

cc_out=$(mktemp creduce_cc_XXXXXX.log)
fc_out=$(mktemp creduce_fc_XXXXXX.log)

# We always check that the reduced file remains valid C code.
set -o pipefail
@CPP@ "@BASE@" 2>&1 | tee $cc_out
set +o pipefail

### Examples of conditions to be maintained by C-Reduce; copy and adapt
#
# Ensure that the C file contains <expr>
# grep -q expr "@BASE@"
#
# Ensure that the compiler output contains <expr>
# grep -q <expr> "$cc_out"
#
###

########## INSERT CONDITION(S) RELATED TO THE SOURCE HERE ##########

##########

set -o pipefail
"@FRAMAC@" "@BASE@" @FCFLAGS@ 2>&1 | tee $fc_out
fc_retcode=$(echo ${PIPESTATUS[0]})
set +o pipefail

### Examples of conditions to be maintained by C-Reduce; copy and adapt
#
# Ensure that Frama-C emits <expr>
# grep -q <expr> "$fc_out"
#
# Ensure that the exit code of Frama_C is <rc>
# test $fc_retcode -eq <rc>
#
###

########## INSERT CONDITION(S) RELATED TO FRAMA-C HERE ##########

##########

### Cleanup
rm -f $cc_out $fc_out
