#!/bin/bash -eu

# [shift_oracles.sh [commit] source.c -- test1.oracle test2.oracle ...]
# modifies the set of oracles w.r.t. [source.c], using `git diff` to
# estimate how many lines were added/removed and then replacing line numbers
# accordingly, to reduce noise when diffing files.
# Note: the oracles must be pristine, because calling multiple times this
# script will modify the oracles at each call.
# Also, because the script uses `git diff`, the modified source must not be
# in the index.

###### Command-line parsing-related code ######

function usage_error {
    echo "usage: $0 [--dry-run] [commit [commit]] modified_source -- oracles"
    echo ""
    echo "       example:"
    echo "                $0 tests/my_test/test.c -- tests/**/*.oracle"
    echo ""
    echo "                  --dry-run: do not run sed, instead print command line"
    echo "       commit numbers/names: optional, passed to 'git diff'"
    echo "            modified_source: a single file that has been modified"
    echo "                    oracles: 1 or more ptests .oracle files"
    exit 1
}

if [ $# -lt 3 ]; then usage_error; fi

if [ "$1" = "--dry-run" ]; then
    dry_run=1
    shift
else
    dry_run=0
fi

file=""
git_diff_args=""
oracles=
for i in $(seq $#); do
    if [ ${!i} = "--" ]; then
        # found '--', use it to determine other arguments
        if [ $i -eq 1 -o $i -eq $# ]; then
            usage_error
        fi
        file_i=$((i-1))
        file="${!file_i}"
        echo "file = $file"
        if [ ! -f "$file" ]; then
            echo "$file is not a file"
            exit 1
        fi
        git_diff_args=${@:1:$((i-1))}
        oracles=("${@:$((i+1))}")
        break
    fi
done
if [ "$file" = "" ]; then # no '--' found, or no file before '--'
    usage_error
fi

###### Actual script code ######

lines=$(wc -l "$file" | cut -d' ' -f1)
line_shift= #empty array
# initialize all lines to "no shift"
for i in $(seq $lines); do
    line_shift[$i]=0
done

# compute the amount to be shifted for each line, using `git diff -U0 source.c`
# the regex is complex because some elements are optional
# (e.g., when the number of modified lines is 1, ",1" is omitted)
start_line=1
first_hunk=1
shift_amount=0
while read -r hunk
do
    IFS=' ' read a b c d e f < <(echo "$hunk")
    first_line1=$a
    #echo "a=$a -- b=$b -- c=$c -- d=$d -- e=$e -- f=$f"
    if [[ $b =~ ^, ]]; then
        n_lines1=$c
        first_line2=$d
        if [[ $e =~ ^, ]]; then n_lines2=$f; else n_lines2=1; fi
    else
        n_lines1=1
        first_line2=$b
        if [[ $c =~ ^, ]]; then n_lines2=$d; else n_lines2=1; fi
    fi
    #echo "first_line1=$first_line1 -- n_lines1=$n_lines1 -- first_line2=$first_line2 -- n_lines2=$n_lines2"
    if [ $first_hunk -eq 1 ]; then
        first_hunk=0
        start_line=$first_line1
        hunk_diff=$((n_lines2 - n_lines1))
        shift_amount=$hunk_diff
        echo "processing hunk: $first_line1,$n_lines1 $first_line2,$n_lines2 (shift amount: $shift_amount)"
    else
        end_line=$first_line1
        for i in $(seq $start_line $((end_line - 1))); do
            line_shift[$i]=$shift_amount
        done
        start_line=$end_line
        hunk_diff=$((n_lines2 - n_lines1))
        shift_amount=$((shift_amount + hunk_diff))
        echo "processing hunk: $first_line1,$n_lines1 $first_line2,$n_lines2 (shift amount: $shift_amount)"
    fi
done < <(git diff --unified=0 $git_diff_args | grep -P '^@@.*@@' | sed -r -e 's/@@ [+-]([0-9]+)(,([0-9]+))? [+-]([0-9]+)(,([0-9]+))? @@.*$/\1 \2 \3 \4 \5 \6/')

if [ $first_hunk -eq 1 ]; then
    echo "error: no hunks found in git diff: git diff $git_diff_args"
    exit 1
fi

# after finishing all hunks, shift until end of file
end_line=$lines
for i in $(seq $start_line $((end_line - 1))); do
    line_shift[$i]=$shift_amount
done

# Note: sources in the Frama-C libc may be printed in two ways, either with
# "share/libc/..." or "FRAMAC_SHARE/libc/...", so we must account for them.
# This may be fixed in a later Frama-C version.
source_in_libc=0
if [[ $file =~ share/libc/(.*) ]]; then
    source_in_libc=1
    source="share/libc/${BASH_REMATCH[1]}"
    source2="FRAMAC_SHARE/libc/${BASH_REMATCH[1]}"
    echo "replacing expressions: \"$source\" or \"$source2\""
else
    source="$file"
    echo "replacing expressions: \"$source\""
fi

# build the large regex that will be given to sed
sed_regex=""
for n in $(seq $lines); do
    if [ ${line_shift[$n]} -ne 0 ]; then
        shifted_n=$((n+line_shift[$n]))
        sed_regex+="s|$source:$n\b|$source:$shifted_n|g; t ;"
        if [ $source_in_libc -ne 0 ]; then
            sed_regex+="s|$source2:$n\b|$source2:$shifted_n|g; t ;"
        fi
    fi
done

if [ $dry_run -eq 1 ] ; then
    echo "dry run: will not run sed"
    echo "final command: sed -i '$sed_regex' ${oracles[@]}"
else
    echo "modifying ${#oracles[@]} oracle(s) in-place..."
    if [ ${#oracles[@]} -gt 500 ]; then
        echo "(this may take a few minutes)"
    fi
    sed -i "$sed_regex" ${oracles[@]}
    echo "done."
fi
