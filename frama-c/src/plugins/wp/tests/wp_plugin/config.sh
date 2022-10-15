#!/bin/sh

ERGO=`alt-ergo -version`
WHY3=`why3 --version`

echo "----------------------------------------------------------"
echo "WP Requirements for Qualif Tests (3)"
echo "----------------------------------------------------------"
echo "1. The Alt-Ergo theorem prover, version ${ERGO}"
echo "2. The ${WHY3}"
echo "----------------------------------------------------------"
