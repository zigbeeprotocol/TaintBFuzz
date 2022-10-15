#!/bin/sh
gcc -C -E -I. -o $3 $2
# Note: some versions of dos2unix (e.g. Busybox) do not have a '-q' flag,
# so we avoid using them
$1 $3 >/dev/null 2>/dev/null
