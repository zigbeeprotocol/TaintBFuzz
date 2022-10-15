#!/bin/sh -eu

# Script used by the test "fc_libc.c"

errors=0

test_dir=$(pwd)
share_libc="$1"
cd "$share_libc"

for A in *.h */*.h; do
    if ! grep -q $A "$test_dir/fc_libc.c"
    then
        echo "missing include in tests/libc/fc_libc.c: $A"
        errors=$((errors+1))
    fi
    if ! grep -q $A __fc_libc.h && [ "${A#__fc_}" = "$A" ]
    then
        echo "missing include in share/libc/__fc_libc.h: $A"
        errors=$((errors+1))
    fi
done

for A in *.c */*.c; do
    if ! grep -q $A __fc_runtime.c "$test_dir/fc_libc.c"
    then
        echo "missing include in share/libc/__fc_runtime.c or tests/libc/fc_libc.c: $A"
        errors=$((errors+1))
    fi
done

if [ $errors -gt 0 ]; then
    echo "found $errors error(s) in libc"
    exit 1
fi
