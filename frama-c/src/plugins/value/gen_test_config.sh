#!/bin/bash

# This scripts creates the ptests config files for the alternative testing
# configurations of Eva. You must create the tests/test_config and
# tests/builtins/test_config yourselves. The other files are created
# accordingly. The syntax for the root test_config files is as follows
# (2 lines):
#
# MACRO: EVA_CONFIG  <options inherited in all tests>
# OPT: @EVA_CONFIG@  <default options, inherited in tests that use STDOPT>

# All tested domains
declare -a domains=(
    "apron"
    "bitwise"
    "equalities"
    "gauges"
    "symblocs"
)
# Option(s) corresponding to each domain
declare -a opts=(
    "-eva-apron-oct -value-msg-key experimental-ok"
    "-eva-bitwise-domain"
    "-eva-equality-domain"
    "-eva-gauges-domain"
    "-eva-symbolic-locations-domain"
)

arraylength=${#domains[@]}

cd tests
CUR=`pwd`

#TODO: générer le test_config de builtins à partir de celui racine ?

for A in  . builtins
do
    cd $CUR/$A

    for (( i=0; i<${arraylength}; i++ ));
    do
        echo "`head -1 test_config` ${opts[$i]}" > test_config_${domains[$i]}
        tail -1 test_config >> test_config_${domains[$i]}
    done
done
