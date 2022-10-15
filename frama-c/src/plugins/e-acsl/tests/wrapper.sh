#!/bin/bash
##########################################################################
#                                                                        #
#  This file is part of the Frama-C's E-ACSL plug-in.                    #
#                                                                        #
#  Copyright (C) 2012-2021                                               #
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

# Wrapper script to compile a test file and execute the resulting binary

# Base dir of this script
BASEDIR="$(realpath `dirname $0`)"

help() {
  printf "wrapper.sh - run e-acsl-gcc.sh and the resulting binary to test E-ACSL
Usage: $0 framac_exe result_dir test_name test_file output_name opts fc_opts filter_cmd
Args:
  framac_exe    @frama-c-exe@ in test_config
  result_dir    @PTEST_RESULT@ in test_config
  test_name     @PTEST_NAME@ in test_config
  test_file     @PTEST_FILE@ in test_config
  output_name   Output file given to LOG in test_config
  opts          Options for e-acsl-gcc.sh
  fc_opts       Options for Frama-C
  filter_cmd    Command to filter the output of the resulting binary
" >&2
  exit 1
}

if [[ $# -ne 8 ]]; then
  printf "Error: wrong number of arguments: 8 expected, got $#\n\n" >&2
  help
fi

# Name the arguments of the script
framac_exe=$1
result_dir=$2
test_name=$3
test_file=$4
output_name=$5
opts=$6
fc_opts=$7
filter_cmd=$8

# Derive output logs from the arguments
out_log=$result_dir/$test_name.res.log
err_log=$result_dir/$test_name.err.log
exec_out_log=$result_dir/$test_name.exec_out.log
exec_err_log=$result_dir/$test_name.exec_err.log
output_log=$result_dir/$output_name

# Compile the test file
$BASEDIR/../scripts/e-acsl-gcc.sh -I $framac_exe \
  -c $opts \
  --frama-c-extra="$fc_opts" \
  -o $result_dir/$test_name.gcc.c \
  -O $result_dir/$test_name \
  $test_file \
  1>$out_log \
  2>$err_log

# Check compilation return code and exit script in case of error
if [[ $? -ne 0 ]]; then
  error_code=$?
  printf "Error while executing e-acsl-gcc.sh\n" > $output_log
  printf "\nSTDOUT:\n" >> $output_log
  cat $out_log >> $output_log
  printf "\nSTDERR:\n" >> $output_log
  cat $err_log >> $output_log
  exit $error_code
fi

# Execute the compiled test file
$result_dir/$test_name.e-acsl 1>$exec_out_log 2>$exec_err_log

# Check execution return code and exit script in case of error
if [[ $? -ne 0 ]]; then
  error_code=$?
  printf "Error while executing $result_dir/$test_name.e-acsl\n" > $output_log
  printf "\nSTDOUT:\n" >> $output_log
  cat $exec_out_log >> $output_log
  printf "\nSTDERR:\n" >> $output_log
  cat $exec_err_log >> $output_log
  exit $error_code
fi

# No error while executing the script, filter stderr before saving it to the
# output log

## Create temporary files
tmp_filter_input=$(mktemp) || (printf "unable to create temp file\n" > $output_log && exit 1)
tmp_filter_output=$(mktemp) || (printf "unable to create temp file\n" > $output_log && exit 1)
cp $exec_err_log $tmp_filter_input

## Split the filter command on character | to extract the subcommands and apply
## the filters one at a time
IFS='|' read -ra filters <<< "$filter_cmd"
for filter in "${filters[@]}"; do
  cat $tmp_filter_input | $filter > $tmp_filter_output
  if [[ $? -ne 0 ]]; then
    error_code=$?
    printf "Error while filtering output with command '$filter'\n" > $output_log
    printf "\nFILTER INPUT:\n" >> $output_log
    cat $tmp_filter_input >> $output_log
    printf "\nFILTER OUTPUT:\n" >> $output_log
    cat $tmp_filter_output >> $output_log
    exit $error_code
  fi
  cp $tmp_filter_output $tmp_filter_input
done

## Filtering done, copy output to the output log and remove temporary files
cp $tmp_filter_output $output_log
rm $tmp_filter_input
rm $tmp_filter_output

exit 0
