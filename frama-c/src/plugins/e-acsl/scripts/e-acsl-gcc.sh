#!/usr/bin/env bash
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

# Convenience wrapper for small runs of E-ACSL Frama-C plugin

# The -e option is not present in the sha-bang on purpose, the error() function
# should be used after each command that may fail.

# Portable realpath using pwd
realpath() {
  if [ -e "$1" ]; then
    if [ -d "$1" ]; then
      (cd "$1" && pwd)
    else
      local name=$(basename "$1")
      local dir=$(cd $(dirname "$1") && pwd)
      echo $dir/$name
    fi
    return 0
  else
    echo "realpath: no such file or directory: '$1'" 1>&2
    return 1
  fi
}

# Print a message to STDERR and exit. If the second argument (exit code)
# is provided and it is '0' then do nothing.
# /!\ Use this function after each command that may fail with the second
# argument set to $?
error () {
  if [ -z "$2" ] || ! [ "$2" = 0 ]; then
    echo "e-acsl-gcc: fatal error: $1" 1>&2
    exit 1;
  fi
}

# Print a warning message to STDERR.
warning () {
  echo "e-acsl-gcc: warning: $1" 1>&2
}

# Base dir of this script
BASEDIR="$(realpath `dirname $0`)"
error "unable to find base dir of script" $?

# True if the script is launched from the E-ACSL sources, false otherwise
is_development_version() {
  test -f "$BASEDIR/../E_ACSL.mli"
}

# Check if a given executable name can be found by in the PATH
has_tool() {
  command -v "$@" >/dev/null 2>&1 && return 0 || return 1
}

# Check if a given executable name is indeed an executable or can be found
# in the $PATH. Abort the execution if not.
check_tool() {
   { has_tool "$1" || test -e "$1"; } || error "No executable '$1' found";
}

# Check if a given Frama-C executable name is indeed an executable, can be found
# in the $PATH, can be found in the same folder than the script, or can be found
# in the binary folder of the development version. Abort the execution if not.
retrieve_framac_path() {
  if has_tool "$1"; then
    echo $(command -v "$1")
  elif [ -e "$1" ]; then
    echo "$1"
  elif [ -e "$BASEDIR/$1" ]; then
    echo "$BASEDIR/$1"
  elif is_development_version && [ -e "$BASEDIR/../../../../bin/$1" ]; then
    echo "$BASEDIR/../../../../bin/$1"
  else
    echo "No executable '$1' or '$BASEDIR/$1' found"
    return 1
  fi
}

# Check whether getopt utility supports long options
check_getopt() {
  local out="$(getopt -l "ab:,cd" -o "x:,y" -- --ab 1 -x 1 --cd  -y \
    | sed "s/[ \']//g")"
  error "system getopt has no support for long option processing" $?
  if ! [ "$out" = "--ab1-x1--cd-y--" ]; then
    error "unexpected output of system getopt" 1
  fi
}

# Check if $1 is positive integer and whether $1 is greater than $2
# Returns $1 is the above holds, otherwise return
#  '-' if $1 is not a positive integer
#  '<' if $1 is a positive integer but it is less than $2
# NB: No checking is done for $2
is_number() {
  local n="$1"
  local lim="$2"

  if [ "$n" -eq "$n" ] 2>/dev/null; then
    if [ "$n" -lt "$lim" ]; then
      echo '<'
    else
      echo $n
    fi
  else
    echo '-'
  fi
}

# Retrieve the zone size for a given zone name and limit
# - $1: the zone name
# - $2: the zone size
# - $3: the minimum zone size
# Return $2 if it is a positive number greater or equal than $3, otherwise
# return an error message with an error code of 1.
get_zone_size() {
  local name="$1"
  local n="$2"
  local lim="$3"

  local zone_size="$(is_number "$n" $lim)"
  case $zone_size in
    '-')
      echo "invalid number for $name: '$n'"
      return 1
    ;;
    '<')
      echo "$name limit less than minimal size [$lim]"
      return 1
    ;;
    *) echo $zone_size
  esac;
  return 0
}

# Split a comma-separated string into a space-separated string, remove
# all duplicates and trailing, leading or multiple spaces
tokenize() {
  echo -n "$@" \
    | sed -e 's/\s//g' -e 's/,/ /g' -e 's/\s\+/\n/g' \
    | sort -u \
    | tr '\n' ' ' \
    | sed 's/\s*$//'
}

# Given a token (first argument) and a list (remaining arguments)
# evaluate to true if the token is in the list, and to false otherwise
has_token() {
  local token="$1"
  local opt
  shift
  for opt in $@; do
    [ "$opt" = "$token" ] && return 0
  done
  return 1
}

# Filter out a token given by the first argument from the list of tokens
# given by the remaining arguments
shift_token() {
  local token="$1"
  shift
  for opt in $@; do
    [ "$opt" = "$token" ] && true || echo $opt
  done
}

# Generate option string for RTE plugin based on the value given via --rte
# and --rte-select flags
rte_options() {
  # Frama-C assertions
  local fc_options="signed-overflow unsigned-overflow \
    signed-downcast unsigned-downcast"
  # RTE assertions
  local rte_options="div float-to-int mem pointer-call shift \
    trivial-annotations"
  # RTE assertions which are negated in all cases except when
  # explicitly specified
  # Option supported by RTE but unsupported in E-ACSL, should
  # always be negated
  local rte_options_unsupported=""
  local rte_options_explicit="trivial-annotations"
  local generated="-rte" # Generated Frama-C options

  # Clean-up option strings
  local full_options="$fc_options $rte_options"
  local input_asserts="$(tokenize "$1")"
  local fselect="$2"

  # If there is 'all' keyword found enable all assertions
  if has_token all $input_asserts; then
    asserts="$full_options"
    for opt in $rte_options_explicit; do
      if ! has_token $opt $input_asserts; then
        asserts="$(shift_token $opt $asserts)"
      fi
    done
  else
    asserts="$input_asserts"
  fi

  if [ -n "$asserts" ]; then
    # Check input options
    local opt
    for opt in $asserts; do
      # Check whether a given input option exists, i.e., found in $full_options
      if ! has_token $opt $full_options; then
        echo "$opt"
        return 1
      fi
    done

    local prefix
    # Generate assertion options for Frama-C (i.e., -warn-* or -no-warn-*)
    for opt in $fc_options; do
      has_token $opt $asserts && prefix="-warn" || prefix="-no-warn"
      generated="$generated $prefix-$opt"
    done

    # Generate assertion options for RTE (i.e., -rte-* or -rte-no-*)
    for opt in $rte_options $rte_options_unsupported; do
      has_token $opt $asserts && prefix="-rte" || prefix="-rte-no"
      generated="$generated $prefix-$opt"
    done

    # Pass -rte-select option of RTE
    if [ -n "$fselect" ]; then
      fselect="$(echo $fselect | sed 's/\s//g')"
      generated="$generated -rte-select=$fselect"
    fi

    echo $generated -then
  fi
  return 0
}

# Output -D flags enabling a given E_ACSL memory model
mmodel_features() {
  local model="$1"

  # Memory model
  case $model in
    bittree) flags="-DE_ACSL_BITTREE_MMODEL" ;;
    segment) flags="-DE_ACSL_SEGMENT_MMODEL" ;;
    *)
      echo "Memory model '$model' is not available in this distribution"
      return 1
    ;;
  esac

  # Temporal analysis
  if [ -n "$OPTION_TEMPORAL" ]; then
    flags="$flags -DE_ACSL_TEMPORAL"
  fi

  # Trigger failures in assertions
  if [ -n "$OPTION_KEEP_GOING" ]; then
    flags="$flags -DE_ACSL_NO_ASSERT_FAIL"
  fi

  # Enable debug mode
  if [ -n "$OPTION_RT_DEBUG" ]; then
    flags="$flags -DE_ACSL_DEBUG"
  fi

  # Set stack shadow size
  if [ -n "$OPTION_STACK_SIZE" ]; then
    flags="$flags -DE_ACSL_STACK_SIZE=$OPTION_STACK_SIZE"
  fi

  # Set heap shadow size
  if [ -n "$OPTION_HEAP_SIZE" ]; then
    flags="$flags -DE_ACSL_HEAP_SIZE=$OPTION_HEAP_SIZE"
  fi

  # Set TLS shadow size
  if [ -n "$OPTION_TLS_SIZE" ]; then
    flags="$flags -DE_ACSL_TLS_SIZE=$OPTION_TLS_SIZE"
  fi

  # Set thread stack size
  if [ -n "$OPTION_THREAD_STACK_SIZE" ]; then
    flags="$flags -DE_ACSL_THREAD_STACK_SIZE=$OPTION_THREAD_STACK_SIZE"
  fi

  # Set runtime verosity flags
  if [ -n "$OPTION_RT_VERBOSE" ]; then
    flags="$flags -DE_ACSL_VERBOSE -DE_ACSL_DEBUG_VERBOSE"
  fi

  if [ -n "$OPTION_FAIL_WITH_CODE" ]; then
    flags="$flags -DE_ACSL_FAIL_EXITCODE=$OPTION_FAIL_WITH_CODE "
  fi

  if [ -n "$OPTION_WEAK_VALIDITY" ]; then
    flags="$flags -DE_ACSL_WEAK_VALIDITY"
  fi

  if [ -n "$OPTION_FREE_VALID_ADDRESS" ]; then
    flags="$flags -DE_ACSL_FREE_VALID_ADDRESS"
  fi

  if [ -n "$OPTION_EXTERNAL_ASSERT" ]; then
    flags="$flags -DE_ACSL_EXTERNAL_ASSERT"
  fi

  if [ -n "$OPTION_EXTERNAL_PRINT_VALUE" ]; then
    flags="$flags -DE_ACSL_EXTERNAL_PRINT_VALUE"
  fi

  if [ -n "$OPTION_NO_TRACE" ]; then
    flags="$flags -DE_ACSL_NO_TRACE"
  fi

  if [ -n "$OPTION_VALIDATE_FORMAT_STRINGS" ]; then
    flags="$flags -DE_ACSL_VALIDATE_FORMAT_STRINGS"
  fi

  echo $flags
}

# Check if system getopt supports long option processing
check_getopt;

# Getopt options
LONGOPTIONS="help,compile,compile-only,debug:,ocode:,oexec:,verbose:,
  frama-c-only,extra-cpp-args:,frama-c-stdlib,full-mmodel,full-mtracking,gmp,
  quiet,logfile:,ld-flags:,cpp-flags:,frama-c-extra:,memory-model:,keep-going,
  frama-c:,gcc:,e-acsl-share:,instrumented-only,rte:,oexec-e-acsl:,concurrency,
  print-mmodels,rt-debug,rte-select:,then,e-acsl-extra:,check,fail-with-code:,
  temporal,weak-validity,stack-size:,heap-size:,zone-sizes:,rt-verbose,
  free-valid-address,external-assert:,assert-print-data,no-assert-print-data,
  external-print-value:,validate-format-strings,no-trace,libc-replacements,
  with-dlmalloc:,dlmalloc-from-sources,dlmalloc-compile-only,
  dlmalloc-compile-flags:,odlmalloc:,ar:,ranlib:,mbits:"
SHORTOPTIONS="h,c,C,d:,D,o:,O:,v:,f,E:,L,M,l:,e:,g,q,s:,F:,m:,I:,G:,X,a:,T,k,V"
# Prefix for an error message due to wrong arguments
ERROR="ERROR parsing arguments:"

# Variables holding getopt options
OPTION_CFLAGS=                           # Compiler flags
OPTION_CPPFLAGS=                         # Preprocessor flags
OPTION_LDFLAGS=                          # Linker flags
OPTION_FRAMAC="frama-c"                  # Frama-C executable name
OPTION_MBITS=                            # Which architecture to compile to
OPTION_CC="gcc"                          # GCC executable name
OPTION_AR="ar"                           # AR executable name
OPTION_RANLIB="ranlib"                   # RANLIB executable name
OPTION_ECHO="set -x"                     # Echo executed commands to STDOUT
OPTION_INSTRUMENT=1                      # Perform E-ACSL instrumentation
OPTION_DEBUG=                            # Set Frama-C debug flag
OPTION_VERBOSE=                          # Set Frama-C verbose flag
OPTION_COMPILE=                          # Compile instrumented program
OPTION_RT_DEBUG=                         # Enable runtime debug features
OPTION_RT_VERBOSE=                       # Set runtime verbosity level
OPTION_OUTPUT_CODE="a.out.frama.c"       # Name of the translated file
OPTION_OUTPUT_EXEC="a.out"               # Generated executable name
OPTION_EACSL_OUTPUT_EXEC=""              # Name of E-ACSL executable
OPTION_EACSL="-e-acsl"                   # Specifies E-ACSL run
OPTION_FRAMA_STDLIB="-no-frama-c-stdlib" # Use Frama-C stdlib
OPTION_FULL_MTRACKING=                   # Instrument as much as possible
OPTION_CONCURRENCY=                      # Activate concurrency support
OPTION_GMP=                              # Use GMP integers everywhere
OPTION_EACSL_MMODELS="segment"           # Memory model used
OPTION_EACSL_SHARE=                      # Custom E-ACSL share directory
OPTION_INSTRUMENTED_ONLY=                # Do not compile original code
OPTION_TEMPORAL=                         # Enable temporal analysis
OPTION_WEAK_VALIDITY=                    # Use notion of weak validity
OPTION_RTE=                              # Enable assertion generation
OPTION_FAIL_WITH_CODE=                   # Exit status code for failures
OPTION_CHECK=                            # Check AST integrity
OPTION_NO_TRACE=                         # Disable trace in debug mode
OPTION_FRAMAC_CPP_EXTRA=                 # Extra CPP flags for Frama-C
OPTION_FREE_VALID_ADDRESS=  # Fail if NULL is used as input to free
OPTION_VALIDATE_FORMAT_STRINGS= # Runtime format string validation
OPTION_LIBC_REPLACEMENTS= # Replace libc functions with RTL definitions
OPTION_RTE_SELECT=        # Generate assertions for these functions only
OPTION_THEN=              # Adds -then in front of -e-acsl in FC command.
OPTION_STACK_SIZE=        # Size of a heap shadow space (in MB)
OPTION_HEAP_SIZE=         # Size of a stack shadow space (in MB)
OPTIONS_TLS_SIZE=         # Size of a TLS shadow space (in MB)
OPTIONS_THREAD_STACK_SIZE=  # Size of a thread stack shadow space (in MB)
OPTION_KEEP_GOING=        # Report failing assertions but do not abort execution
OPTION_EXTERNAL_ASSERT="" # Use custom definition of assert function
OPTION_ASSERT_PRINT_DATA= # Print data contributing to a failed runtime assertion
OPTION_EXTERNAL_PRINT_VALUE="" # Use custom definition of printing value function
OPTION_WITH_DLMALLOC=""                  # Use provided dlmalloc library
OPTION_DLMALLOC_FROM_SOURCES=            # Compile dlmalloc from sources
OPTION_DLMALLOC_COMPILE_ONLY=            # Only compile dlmalloc
OPTION_DLMALLOC_COMPILE_FLAGS="-O2 -g3"  # Dlmalloc compilation flags
OPTION_OUTPUT_DLMALLOC=""                # Name of the compiled dlmalloc

SUPPORTED_MMODELS="bittree,segment" # Supported memory model names
MIN_STACK=16 # Minimal size of a tracked program stack
MIN_HEAP=64 # Minimal size of a tracked program heap
MIN_TLS=1 # Minimal size of a tracked program TLS
MIN_THREAD_STACK=4 # Minimal size of a tracked program thread stack

manpage() {
  printf "e-acsl-gcc.sh - instrument and compile C files with E-ACSL
Usage: e-acsl-gcc.sh [options] files
Options:
  -h         show this help page
  -c         compile instrumented code
  -C         assume that the input files have already been instrumented
  -l         pass additional options to the linker
             (e.g. -l -lm)
  -e         pass additional options to the prepreprocessor
             (e.g. -e \"-DPI=3.14 -DE_ACSL_DEBUG_ASSERT\")
  -E         pass additional arguments to the Frama-C preprocessor
             (e.g. -E \"-Iinclude -DMACRO=1\")
  -F         pass additional options to the Frama-C command line
             (e.g. -F -c11)
  -o <file>  output the generated code to <file> [a.out.frama.c]
  -O <file>  output the generated executables to <file> [a.out, a.out.e-acsl]
  -M         maximize memory-related instrumentation
  -g         always use GMP integers instead of C integral types
  -q         suppress any output except for errors and warnings
  -s <file>  redirect all output to <file>
  -I <file>  specify Frama-C executable [frama-c]
  -G <file>  specify C compiler executable [gcc]

Notes:
  This help page shows only basic options.
  See man (1) e-acsl-gcc.sh for full up-to-date documentation.\n"
  exit 1
}

# Run getopt
ARGS=`getopt -n "$ERROR" -l "$LONGOPTIONS" -o "$SHORTOPTIONS" -- "$@"`

# Print and exit if getopt fails
if [ $? != 0 ]; then
  exit 1;
fi

# Set all options in $@ before -- and other after
eval set -- "$ARGS"

# Switch statements for other options
for i in $@
do
  case "$i" in
    # Do compile instrumented code
    --help|-h)
      shift;
      manpage;
    ;;
    # Do not echo commands to STDOUT
    # Set log and debug flags to minimal verbosity levels
    --quiet|-q)
      shift;
      OPTION_ECHO=
      OPTION_DEBUG="-e-acsl-debug 0"
      OPTION_VERBOSE="-e-acsl-verbose 0"
    ;;
    # Redirect all output to a given file
    --logfile|-s)
      shift;
      exec > $1
      exec 2> $1
      shift;
    ;;
    # Enable runtime debug features, i.e., compile unoptimized executable
    # with assertions, extra checks and other debug features
    --rt-debug|-D)
      shift
      OPTION_RT_DEBUG=1
      OPTION_CHECK=1
    ;;
    --rt-verbose|-V)
      shift;
      OPTION_RT_VERBOSE=1
    ;;
    # Pass an option to a Frama-C invocation
    --frama-c-extra|-F)
      shift;
      FRAMAC_FLAGS="$FRAMAC_FLAGS $1"
      shift;
    ;;
    # Do compile instrumented code
    --compile|-c)
      shift;
      OPTION_COMPILE=1
    ;;
    # Set Frama-C debug flag
    --debug|-d)
      shift;
      if [ "$1" -eq "$1" ] 2>/dev/null; then
        OPTION_DEBUG="-e-acsl-debug $1"
      else
        error "-d|--debug option requires integer argument"
      fi
      shift;
    ;;
    # Set Frama-C verbose flag
    --verbose|-v)
      shift;
      if [ "$1" -eq "$1" ] 2>/dev/null; then
        OPTION_VERBOSE="-e-acsl-verbose $1"
      else
        error "-v|--verbose option requires integer argument"
      fi
      shift;
    ;;
    # Specify the name of the default source file where instrumented
    # code is to be written
    --ocode|-o)
      shift;
      OPTION_OUTPUT_CODE="$1"
      shift
    ;;
    # Specify the base name of the executable generated from the
    # instrumented and non-instrumented sources.
    --oexec|-O)
      shift;
      OPTION_OUTPUT_EXEC="$1"
      shift
    ;;
    # Specify the output name of the E-ACSL generated executable
    --oexec-e-acsl)
      shift;
      OPTION_EACSL_OUTPUT_EXEC="$1"
      shift;
    ;;
    # Additional CPP arguments
    --extra-cpp-args|-E)
      shift;
      OPTION_FRAMAC_CPP_EXTRA="$OPTION_FRAMAC_CPP_EXTRA $1"
      shift;
    ;;
    # Additional flags passed to the linker
    --ld-flags|-l)
      shift;
      OPTION_LDFLAGS="$OPTION_LDFLAGS $1"
      shift;
    ;;
    # Additional flags passed to the pre-processor (compile-time)
    --cpp-flags|-e)
      shift;
      OPTION_CPPFLAGS="$OPTION_CPPFLAGS $1"
      shift;
    ;;
    # Do not perform the instrumentation, only compile the provided sources
    # This option assumes that the source files provided at input have
    # already been instrumented
    --compile-only|-C)
      shift;
      OPTION_INSTRUMENT=
      OPTION_COMPILE="1"
    ;;
    # Run only Frama-C related instrumentation
    --frama-c-only|-f)
      shift;
      OPTION_EACSL=
    ;;
    # Do not compile original source file
    --instrumented-only|-X)
      shift;
      OPTION_INSTRUMENTED_ONLY=1
    ;;
    # Do use Frama-C stdlib, which is the default behaviour of Frama-C
    --frama-c-stdlib|-L)
      shift;
      OPTION_FRAMA_STDLIB="-frama-c-stdlib"
    ;;
    # Use as much memory-related instrumentation as possible
    -M|--full-mtracking|--full-mmodel)
      if [ "$i" = "--full-mmodel" ]; then
        warning "--full-mmodel is a deprecated alias for option --full-mtracking."
        warning "Please use --full-mtracking instead."
      fi
      shift;
      OPTION_FULL_MTRACKING="-e-acsl-full-mtracking"
    ;;
    # Use GMP everywhere
    -g|--gmp)
      shift;
      OPTION_GMP="-e-acsl-gmp-only"
    ;;
    # Concurrency support
    --concurrency)
      shift;
      OPTION_CONCURRENCY="-e-acsl-concurrency"
    ;;
    # Supply Frama-C executable name
    -I|--frama-c)
      shift;
      OPTION_FRAMAC="$(command -v $1 || echo $1)"
      shift;
    ;;
    # Supply GCC executable name
    -G|--gcc)
      shift;
      OPTION_CC="$(command -v $1 || echo $1)"
      shift;
    ;;
    # Specify EACSL_SHARE directory (where C runtime library lives) by hand
    # rather than compute it
    --e-acsl-share)
      shift;
      OPTION_EACSL_SHARE="$1"
      shift;
    ;;
    # Runtime assertion generation
    --rte|-a)
      shift;
      OPTION_RTE="$1"
      shift;
    ;;
    # Runtime assertion generation for given functions only
    --rte-select|-A)
      shift;
      OPTION_RTE_SELECT="$1"
      shift;
    ;;
    # Check AST integrity (mostly for developers of E-ACSL)
    --check)
      OPTION_CHECK=1
      FRAMAC_FLAGS="-check $FRAMAC_FLAGS"
      shift;
    ;;
    # Enable instrumentations of temporal validity analysis
    -T|--temporal)
      shift;
      OPTION_TEMPORAL=-e-acsl-temporal-validity
    ;;
    # A memory model  (or models) to link against
    -m|--memory-model)
      shift;
      # Convert comma-separated string into white-space separated string
      OPTION_EACSL_MMODELS="`echo $1 | sed -s 's/,/ /g'`"
      error "unable to parse '$1' with sed" $?
      shift;
    ;;
    # Print names of the supported memody models.
    --print-mmodels)
      shift;
      echo $SUPPORTED_MMODELS
      exit 0
    ;;
    # Separate extra Frama-C flags from e-acsl launch with -then.
    --then)
      shift;
      OPTION_THEN=-then
    ;;
    # Extra E-ACSL options
    --e-acsl-extra)
      shift;
      OPTION_EACSL="$1 $OPTION_EACSL"
      shift;
    ;;
    # Report failing assertions but do not abort execution
    -k|--keep-going)
      shift;
      OPTION_KEEP_GOING=1
    ;;
    # Exit with a given code on assertion failure instead of raising abort
    --fail-with-code)
      shift;
      if [ "$1" -eq "$1" ] 2>/dev/null; then
        OPTION_FAIL_WITH_CODE="$1"
      else
        error "--fail-with-code option requires integer argument"
      fi
      shift;
    ;;
    # Use notion of weak validity
    --free-valid-address)
      shift;
      OPTION_FREE_VALID_ADDRESS=1
    ;;
    # Use notion of weak validity
    --weak-validity)
      shift;
      OPTION_WEAK_VALIDITY=1
    ;;
    # Set heap shadow size
    --heap-size)
      warning "--heap-size is a deprecated option."
      warning "Please use --zone-sizes instead."
      shift;
      zone_size="$(is_number "$1" $MIN_HEAP)"
      case $zone_size in
        '-') error "invalid number: '$1'" ;;
        '<') error "heap limit less than minimal size [$MIN_HEAP"]
          ;;
        *) OPTION_HEAP_SIZE=$zone_size ;;
      esac;
      shift;
    ;;
    # Set stack shadow size
    --stack-size)
      warning "--stack-size is a deprecated option."
      warning "Please use --zone-sizes instead."
      shift;
      zone_size="$(is_number "$1" $MIN_STACK)"
      case $zone_size in
        '-') error "invalid number: '$1'" ;;
        '<') error "stack limit less than minimal size [$MIN_STACK"] ;;
        *) OPTION_STACK_SIZE=$zone_size ;;
      esac;
      shift;
    ;;
    --zone-sizes)
      shift;
      zone_help_msg="available zone names for option --zone-sizes:
  - stack
  - heap
  - tls
  - thread-stack
The size is given in MB.
"
      IFS=',' read -ra sizes <<< "$1"
      for size in "${sizes[@]}"; do
        IFS=':' read -ra size_arr <<< "$size"
        if [ "${#size_arr[@]}" -eq "2" ]; then
          zone_name="${size_arr[0]}"
          zone_size="${size_arr[1]}"
          case $zone_name in
            stack)
              OPTION_STACK_SIZE="$(get_zone_size $zone_name "$zone_size" $MIN_STACK)"
              error "$OPTION_STACK_SIZE" $?
            ;;
            heap)
              OPTION_HEAP_SIZE="$(get_zone_size $zone_name "$zone_size" $MIN_HEAP)"
              error "$OPTION_HEAP_SIZE" $?
            ;;
            tls)
              OPTION_TLS_SIZE="$(get_zone_size $zone_name "$zone_size" $MIN_TLS)"
              error "$OPTION_TLS_SIZE" $?
            ;;
            thread-stack)
              OPTION_THREAD_STACK_SIZE="$(get_zone_size $zone_name "$zone_size" $MIN_THREAD_STACK)"
              error "$OPTION_THREAD_STACK_SIZE" $?
            ;;
            *)
              error "invalid zone name: '$zone_name'
$zone_help_msg"
            ;;
          esac
        elif [ "${#size_arr[@]}" -eq "1" ] && [ "${size_arr[0]}" == "help" ]; then
          printf "e-acsl-gcc.sh - $zone_help_msg"
          exit 1
        else
          error "invalid zone size format: '$size' (expected 'name:number')"
        fi
      done
      shift;
    ;;
    # Custom runtime assert function
    --external-assert)
      shift;
      OPTION_EXTERNAL_ASSERT="$1"
      shift;
    ;;
    # Print data contributing to a failed runtime assertion
    --assert-print-data)
      shift;
      OPTION_ASSERT_PRINT_DATA="-e-acsl-assert-print-data"
    ;;
    --no-assert-print-data)
      shift;
      OPTION_ASSERT_PRINT_DATA="-e-acsl-no-assert-print-data"
    ;;
    # Custom function for printing value
    --external-print-value)
      shift;
      OPTION_EXTERNAL_PRINT_VALUE="$1"
      shift;
    ;;
    # Check output format functions
    --validate-format-strings)
      shift;
      OPTION_VALIDATE_FORMAT_STRINGS="-e-acsl-validate-format-strings"
    ;;
    # Replace some unsafe libc functions (such as strcpy, strcat) with
    # RTL definitions and internal error checking
    --libc-replacements)
      shift;
      OPTION_LIBC_REPLACEMENTS="-e-acsl-replace-libc-functions"
    ;;
    # Disable trace in debug mode
    --no-trace)
      shift
      OPTION_NO_TRACE=1
    ;;
    --ar)
      shift;
      OPTION_AR="$(command -v $1 || echo $1)"
      shift;
    ;;
    --ranlib)
      shift;
      OPTION_RANLIB="$(command -v $1 || echo $1)"
      shift;
    ;;
    --with-dlmalloc)
      shift;
      OPTION_WITH_DLMALLOC="$1"
      shift;
    ;;
    --dlmalloc-from-sources)
      shift;
      OPTION_DLMALLOC_FROM_SOURCES=1
    ;;
    --dlmalloc-compile-only)
      shift;
      OPTION_INSTRUMENT=
      OPTION_DLMALLOC_COMPILE_ONLY=1
    ;;
    --dlmalloc-compile-flags)
      shift;
      OPTION_DLMALLOC_COMPILE_FLAGS="$1"
      shift;
    ;;
    --odlmalloc)
      shift;
      OPTION_OUTPUT_DLMALLOC="$1"
      shift;
    ;;
    # Architecture selection
    --mbits)
      shift;
      OPTION_MBITS="$1"
      shift;
    ;;
  esac
done
shift;

# Bail if no files to translate are given and we're not trying to only compile
# dlmalloc
if [ -z "$1" -a "$OPTION_DLMALLOC_COMPILE_ONLY" != "1" ]; then
  error "no input files";
fi

# Check Frama-C and GCC executable names
OPTION_FRAMAC="$(retrieve_framac_path "$OPTION_FRAMAC")"
error "$OPTION_FRAMAC" $?
check_tool "$OPTION_CC"

# Frama-C directories
FRAMAC="$OPTION_FRAMAC"
: ${FRAMAC_SHARE:="`$FRAMAC -no-autoload-plugins -print-share-path`"}
: ${FRAMAC_PLUGIN:="`$FRAMAC -no-autoload-plugins -print-plugin-path`"}

# Check if this is a development or an installed version
if is_development_version; then
  # Development version
  DEVELOPMENT="$(realpath "$BASEDIR/..")"
  error "unable to find parent dir of base dir" $?
  # Check if the project has been built, as if this is a non-installed
  # version that has not been built Frama-C will fallback to an installed one
  # for instrumentation but still use local RTL
  error "Plugin in $DEVELOPMENT not compiled" \
    `test -f "$DEVELOPMENT/META.frama-c-e_acsl" -o \
          -f "$FRAMAC_PLUGIN/META.frama-c-e_acsl"; echo $?`
  EACSL_SHARE="$DEVELOPMENT/share/e-acsl"
  EACSL_LIB="$DEVELOPMENT/lib"
  EACSL_CONTRIB="$DEVELOPMENT/contrib"
  # Add the project directory to FRAMAC_PLUGINS,
  # otherwise Frama-C uses an installed version
  if test -f "$DEVELOPMENT/META.frama-c-e_acsl"; then
    FRAMAC_FLAGS="-add-path=$DEVELOPMENT/top -add-path=$DEVELOPMENT $FRAMAC_FLAGS";
  fi
else
  # Installed version. FRAMAC_SHARE should not be used here as Frama-C
  # and E-ACSL may not be installed to the same location
  EACSL_SHARE="$BASEDIR/../share/frama-c/e-acsl"
  EACSL_LIB="$BASEDIR/../lib/frama-c/e-acsl"
  EACSL_CONTRIB="$BASEDIR/../share/frama-c/e-acsl/contrib"
fi

# Architecture-dependent flags. Since by default Frama-C uses 32-bit
# architecture we need to make sure that same architecture is used for
# instrumentation and for compilation.
if [ -n "$OPTION_MBITS" ]; then
  MACHDEPFLAGS="$OPTION_MBITS"
else
  MACHDEPFLAGS="`getconf LONG_BIT`"
fi
# Check if getconf gives out the value accepted by Frama-C/GCC
echo "$MACHDEPFLAGS" | grep '16\|32\|64' 2>&1 >/dev/null \
  || error "$MACHDEPFLAGS-bit architecture not supported"
# -machdep option sent to Frama-C
MACHDEP="-machdep gcc_x86_$MACHDEPFLAGS"
# Macro for correct preprocessing of Frama-C generated code
CPPMACHDEP="-D__FC_MACHDEP_X86_$MACHDEPFLAGS"
# GCC machine option
GCCMACHDEP="-m$MACHDEPFLAGS"

# RTE flags
RTE_FLAGS="$(rte_options "$OPTION_RTE" "$OPTION_RTE_SELECT")"
error "Invalid argument '$RTE_FLAGS' to --rte|-a option" $?

# Frama-C and related flags
# Additional flags passed to Frama-C preprocessor via `-cpp-extra-args`
#  -std=c99 -D_DEFAULT_SOURCE: use C99 + default features. This is important
#    in OSX which by default enables `blocks` unsupported by Frama-C
#  -D__NO_CTYPE: prevent `isupper` (and similar functions) from being used as
#    macros, otherwise E-ACSL cannot track them at runtime
FRAMAC_CPP_EXTRA="\
 -std=c99 -D_DEFAULT_SOURCE -D__NO_CTYPE $CPPMACHDEP\
 $OPTION_FRAMAC_CPP_EXTRA"
EACSL_MMODEL="$OPTION_EACSL_MMODEL"

# Re-set EACSL_SHARE  directory is it has been given by the user
if [ -n "$OPTION_EACSL_SHARE" ]; then
  EACSL_SHARE="$OPTION_EACSL_SHARE"
fi

if [ -n "$OPTION_THEN" ]; then
  FRAMAC_FLAGS="-e-acsl-share=$EACSL_SHARE $FRAMAC_FLAGS";
fi

# Select optimization flags for both instrumented and noon-instrumented code
# compilation
if [ -n "$OPTION_RT_DEBUG" ]; then
  OPT_CFLAGS="-g3 -O0 -fno-omit-frame-pointer"
  OPT_LDFLAGS="-no-pie"
else
  OPT_CFLAGS="-g -O2"
  OPT_LDFLAGS=""
fi

# Concurrency support
if [ -n "$OPTION_CONCURRENCY" ]; then
  OPT_CPPFLAGS="$OPT_CPPFLAGS -DE_ACSL_CONCURRENCY_PTHREAD"
  OPT_LDFLAGS="$OPT_LDFLAGS -pthread"
fi

# Gcc and related flags
CC="$OPTION_CC"
CFLAGS="$OPTION_CFLAGS
  -std=c99 $GCCMACHDEP $OPT_CFLAGS
  -fno-builtin -fno-merge-constants
  -Wall \
  -Wno-long-long \
  -Wno-attributes \
  -Wno-nonnull \
  -Wno-undef \
  -Wno-unused \
  -Wno-unused-function \
  -Wno-unused-result \
  -Wno-unused-value \
  -Wno-unused-function \
  -Wno-unused-variable \
  -Wno-unused-but-set-variable \
  -Wno-implicit-function-declaration \
  -Wno-empty-body"

# Disable extra warning for clang
if [ "`basename $CC`" = 'clang' ]; then
  CFLAGS="-Wno-unknown-warning-option \
    -Wno-extra-semi \
    -Wno-tautological-compare \
    -Wno-gnu-empty-struct \
    -Wno-incompatible-pointer-types-discards-qualifiers"
fi

CPPFLAGS="$OPTION_CPPFLAGS
  $OPT_CPPFLAGS"
LDFLAGS="$OPTION_LDFLAGS
  $OPT_LDFLAGS"

# Dlmalloc
if [ -n "$OPTION_WITH_DLMALLOC" ]; then
  if [ "$OPTION_DLMALLOC_FROM_SOURCES" = "1" ]; then
    error "use either --with-dlmalloc FILE or --dlmalloc-from-sources"
  fi
  if [ "$OPTION_DLMALLOC_COMPILE_ONLY" = "1" ]; then
    error "use either --with-dlmalloc FILE or --dlmalloc-compile-only"
  fi

  # Use provided dlmalloc library
  DLMALLOC_LIB_PATH="$OPTION_WITH_DLMALLOC"
else
  # Use distributed dlmalloc library
  DLMALLOC_LIB_PATH="$EACSL_LIB/libeacsl-dlmalloc.a"
fi

if [ "$OPTION_DLMALLOC_FROM_SOURCES" = "1" -o \
     "$OPTION_DLMALLOC_COMPILE_ONLY" = "1" ]; then
  # Check ar and ranlib tools
  check_tool "$OPTION_AR"
  check_tool "$OPTION_RANLIB"
  AR="$OPTION_AR"
  RANLIB="$OPTION_RANLIB"

  # Create a temporary directory to build dlmalloc. That directory will be
  # removed when exiting the script
  DLMALLOC_TMP_DIR=$(mktemp -d) || error "unable to create temp directory."
  trap 'rm -rf "$DLMALLOC_TMP_DIR"' EXIT

  DLMALLOC_SRC="$EACSL_CONTRIB/libdlmalloc/dlmalloc.c"
  DLMALLOC_OBJ="$DLMALLOC_TMP_DIR/dlmalloc.o"

  if [ -n "$OPTION_OUTPUT_DLMALLOC" ]; then
    DLMALLOC_LIB_PATH="$OPTION_OUTPUT_DLMALLOC"
  else
    DLMALLOC_LIB_PATH="$DLMALLOC_TMP_DIR/libeacsl-dlmalloc.a"
  fi

  DLMALLOC_FLAGS="\
    $GCCMACHDEP \
    -DHAVE_MORECORE=0 \
    -DHAVE_MMAP=1  \
    -DNO_MALLINFO=1 \
    -DNO_MALLOC_STATS=1 \
    -DMSPACES=1 \
    -DONLY_MSPACES \
    -DMALLOC_ALIGNMENT=32 \
    -DMSPACE_PREFIX=__e_acsl_ \
    -DUSE_LOCKS=1 \
    -DUSE_SPIN_LOCKS=1 \
    $OPTION_DLMALLOC_COMPILE_FLAGS
  "

  # Compile dlmalloc from sources
  ($OPTION_ECHO; \
   $CC -c $DLMALLOC_SRC $DLMALLOC_FLAGS -o$DLMALLOC_OBJ)
  error "fail to compile dlmalloc." $?
  ($OPTION_ECHO; \
   $AR crus $DLMALLOC_LIB_PATH $DLMALLOC_OBJ)
  error "fail to create dlmalloc archive library." $?
  ($OPTION_ECHO; \
   $RANLIB $DLMALLOC_LIB_PATH)
  error "fail to generate dlmalloc archive index." $?

  # Exit if dlmalloc-compile-only has been used
  if [ "$OPTION_DLMALLOC_COMPILE_ONLY" = "1" ]; then
    # If dlmalloc-compile-only is used with instrumented-only or compile,
    # display a warning message
    if [ -n "$OPTION_COMPILE" -o -n "$OPTION_INSTRUMENT" -o \
         -n "$OPTION_INSTRUMENTED_ONLY" ]; then
      warning "--dlmalloc-compile-only was used, the instrumentation and \
compilation of the source code won't be run."
    fi

    exit 0;
  fi
fi

# Extra Frama-C Flags E-ACSL needs
FRAMAC_FLAGS="$FRAMAC_FLAGS \
  -remove-unused-specified-functions"

if [ -n "$OPTION_VALIDATE_FORMAT_STRINGS" ]; then
  FRAMAC_FLAGS="$FRAMAC_FLAGS \
    -variadic-no-translation"
fi

# C, CPP and LD flags for compilation of E-ACSL-generated sources
EACSL_CFLAGS="$OPTION_EXTERNAL_ASSERT $OPTION_EXTERNAL_PRINT_VALUE"
EACSL_CPPFLAGS="-I$EACSL_SHARE"
EACSL_LDFLAGS="$DLMALLOC_LIB_PATH -lgmp -lm"

# Output file names
OUTPUT_CODE="$OPTION_OUTPUT_CODE" # E-ACSL instrumented source
OUTPUT_EXEC="$OPTION_OUTPUT_EXEC" # Output name of the original executable

# Output name of E-ACSL-modified executable
if [ -z "$OPTION_EACSL_OUTPUT_EXEC" ]; then
  EACSL_OUTPUT_EXEC="$OPTION_OUTPUT_EXEC.e-acsl"
else
  EACSL_OUTPUT_EXEC="$OPTION_EACSL_OUTPUT_EXEC"
fi

# Build E-ACSL plugin argument string
if [ -n "$OPTION_EACSL" ]; then
  EACSL_FLAGS="
    $OPTION_THEN
    $OPTION_EACSL
    $OPTION_GMP
    $OPTION_LIBC_REPLACEMENTS
    $OPTION_FULL_MTRACKING
    $OPTION_TEMPORAL
    $OPTION_VERBOSE
    $OPTION_DEBUG
    $OPTION_VALIDATE_FORMAT_STRINGS
    $OPTION_ASSERT_PRINT_DATA
    $OPTION_CONCURRENCY
    -e-acsl-share="$EACSL_SHARE"
    -then-last"
fi

# Instrument
if [ -n "$OPTION_INSTRUMENT" ]; then
  ($OPTION_ECHO; \
    $FRAMAC \
    $FRAMAC_FLAGS \
    $MACHDEP \
    -cpp-extra-args="$FRAMAC_CPP_EXTRA" \
    $OPTION_FRAMA_STDLIB \
    "$@" \
    $RTE_FLAGS \
    $EACSL_FLAGS \
    -print -ocode "$OPTION_OUTPUT_CODE");
    error "aborted by Frama-C" $?;
fi

# Compile
if [ -n "$OPTION_COMPILE" ]; then
  # Compile original source code
  # $OPTION_INSTRUMENT is set -- both, instrumented and original, sources are
  # available. Do compile the original program unless instructed to not do so
  # by a user
  if [ -n "$OPTION_INSTRUMENT" ]; then
    if [ -z "$OPTION_INSTRUMENTED_ONLY" ]; then
      ($OPTION_ECHO; $CC $CPPFLAGS $CFLAGS "$@" -o "$OUTPUT_EXEC" $LDFLAGS);
      error "fail to compile/link un-instrumented code" $?;
    fi
  # If $OPTION_INSTRUMENT is unset then the sources are assumed to be already
  # instrumented, so skip compilation of the original files
  else
    OUTPUT_CODE="$@"
  fi

  # Compile and link E-ACSL-instrumented file with all models specified
  for model in $OPTION_EACSL_MMODELS; do
    # If multiple models are specified then the generated executable
    # is appended a '-MODEL' suffix, where MODEL is the name of the memory
    # model used
    if ! [ "`echo $OPTION_EACSL_MMODELS | wc -w`" = 1 ]; then
      OUTPUT_EXEC="$EACSL_OUTPUT_EXEC-$model"
    else
      OUTPUT_EXEC="$EACSL_OUTPUT_EXEC"
    fi
    # RTL sources
    EACSL_RTL="$EACSL_SHARE/e_acsl_rtl.c"
    EACSL_MMODEL_FEATURES="$(mmodel_features $model)"
    error "$EACSL_MMODEL_FEATURES" $?
    ($OPTION_ECHO;
     $CC \
       $EACSL_MMODEL_FEATURES \
       $CFLAGS $CPPFLAGS \
       $EACSL_CFLAGS $EACSL_CPPFLAGS \
       -o "$OUTPUT_EXEC" \
       $OUTPUT_CODE \
       $EACSL_RTL \
       $LDFLAGS \
       $EACSL_LDFLAGS)
    error "fail to compile/link instrumented code" $?
  done
fi
exit 0;
