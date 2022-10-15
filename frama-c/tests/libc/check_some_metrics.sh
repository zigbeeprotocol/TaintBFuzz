#!/usr/bin/env bash

# Perform some checks on the output of the Metrics plugin, but avoiding
# too many details which cause conflicts during merge of libc branches.
#
# This script expects a multiple of 5 arguments containing the expressions
# to compare for each 'run' of metrics: the first argument will be compared
# to the number of defined functions; the second argument to the number of
# specified functions; etc, until the 5th. Then, the 6th argument will
# correspond to the following run of metrics, until the 10th; and so on.
#
# This test reads stdin and expects to find the output of one or more metrics
# runs, which it then reads line by line, parses the relevant numbers,
# and compares them to the expressions passed as arguments.

echo "Checking libc metrics..."

set -eu

declare -A checks
runs=0
cur_arg=0
if [ $(($# % 5)) != 0 ]; then
    echo "error: expected a multiple of 5 arguments, got $#"
    exit 1
fi
for ((run=1; run<=$(( ( $#  ) / 5)); run++))
do
    for ((i=1;i<=5;i++))
    do
        cur_arg=$((cur_arg+1))
        checks["${run}-$i"]="${!cur_arg}"
    done
    runs=$((runs+1))
done

regex=" *([a-zA-Z0-9\'][a-zA-Z0-9\' -]+)+ +\(([0-9]+)\)"

# tbl: stores mappings (<run>-<title>, <count>), where <run> is the
# metrics run (1 or 2), <title> is the Metrics title for the category,
# and <count> is the number between parentheses reported by Metrics.
declare -A tbl

check () { # $1: state, $2: title, $3: expected cond
    key="$1-$2"
    count=${tbl[$key]-0}
    test_exp='! [ $count $3 ]'
    if eval $test_exp; then
        echo "warning: [metrics run $1]: $2: expected $3, got $count"
    fi
}

# read stdin line by line and store relevant ones
# uses the '[metrics]' prefix to detect when a new run starts
state=0
lines=0
while IFS= read -r line; do
    lines=$((lines+1))
    if [[ $line =~ "[metrics]" ]]; then
        state=$((state + 1))
    fi
    if [[ $line =~ $regex ]]; then
        title="${BASH_REMATCH[1]}"
        count=${BASH_REMATCH[2]}
        tbl["$state-$title"]=$count
    fi
done

if [ "$state" == 0 ]; then
    echo "error: no metrics output parsed."
    exit 1
fi

# conditions to be checked

for ((run=1; run<=runs; run++))
do
    echo "Checking run $run..."
    check $run "Defined functions" "${checks[$run-1]}"
    check $run "Specified-only functions" "${checks[$run-2]}"
    check $run "Undefined and unspecified functions" "${checks[$run-3]}"
    check $run "'Extern' global variables" "${checks[$run-4]}"
    check $run "Potential entry points" "${checks[$run-5]}"
done

echo "Finished checking libc metrics."
