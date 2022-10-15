#!/bin/bash -eu

if [ -z ${TARGETS+x} ]; then
    TARGETS="float value idct builtins"
fi
if [ -z ${CONFIGS+x} ]; then
    CONFIGS="apron equality bitwise symblocs gauges octagon multidim"
fi
ARGS="${@-}"

# has_target returns 0 if at least one of the arguments is a target
# (i.e. not an option such as "-j 8"). If so, do not run tests
# for all default targets, only for the specified target(s)
has_target=0
# sets has_target=0
function has_target() {
    local __has_target=1
    for f in $@; do
        __re="\\b$f\\b" # match argument as whole word
        if [[ "$f" =~ \.[ci]$ || \
            ( "$f" =~ ^[A-Za-z] && "${TARGETS[@]}" =~ $__re ) ]]; then
            __has_target=0
        fi
    done
    return $__has_target
}

if has_target ${ARGS[@]}; then
    TARGETS_AND_ARGS="${ARGS[@]}"
else
    TARGETS_AND_ARGS="${TARGETS[@]} ${ARGS[@]}"
fi

echo "CONFIGS: ${CONFIGS[@]}"
for config in ${CONFIGS[@]}
do
    set -x
    ./bin/ptests.opt -config $config ${TARGETS_AND_ARGS[@]}
    { set +x; } 2>&-
done
