#!/bin/sh
##########################################################################
#                                                                        #
#  This file is part of Frama-C.                                         #
#                                                                        #
#  Copyright (C) 2007-2022                                               #
#    CEA (Commissariat à l'énergie atomique et aux énergies              #
#         alternatives)                                                  #
#                                                                        #
#  All rights reserved.                                                  #
#  Contact CEA LIST for licensing.                                       #
#                                                                        #
##########################################################################


APPLINAME="$0"
HEADACHE=$(dirname $APPLINAME)/headache.sh

Usage() {
  APPLI=$(basename $APPLINAME)
  echo "Usage: $APPLI <option>* <headers-spec> <header-dir>  [<target-dir>] [<headache-config>]"
  echo "  <option>"
  echo "    --dry-run: shows the commands to perform without any file modification"
  echo "    --max-procs <N>: runs up to <N> jobs in parallel."
  echo "    --parallel: uses 'parallel' software instead of 'xargs'"
  echo "  <target-dir>: root pathname to the files to modify"
  echo "                default to ."
  echo "  <header-dir>: directory that should contents header files"
  echo "  <headache-config>: headache config file"
  echo "                default to ./headers"
  echo "  <headers-spec>: defines header files to apply on files".
  echo "    The format of <headers-spec> file is checked before doing anything."
  echo "    Syntax:"
  echo "      <line format>= <header-file> ':' <file-to-modify> '\n'"
  echo "                   | '.ignore' ':' <ignored-file> '\n'"
  echo "                   | '#' <comment-line> '\n'"
  echo "                   | [':'] '\n'"
  echo "     Ignored files are not modified by the script ${APPLI}."

  exit 1
}

Requires () {
# Looking for executables
  for File in "$@" ; do
    where=$(which $File)
    if [ "$?" != "0" ] ; then
      echo "Error: executable not found: $File"
      exit 1
    fi
  done
}

SetVariables() {
  FILE=$1
  HEADER_SRC=$2
  TARGET_DIR=${3-.}
  HEADACHE_CONFIG=${4-./headers/headache_config.txt}
  if [ "$5" != "" ] ; then
    echo "Error: too much arguments."
    exit 1
  fi
  if [ "${MAX_PROCS}" = "" ] && [ -f /proc/cpuinfo ] ; then
    # Linux system
    MAX_PROCS=$(cat /proc/cpuinfo | grep -c processor)
  fi
  if [ "${MAX_PROCS}" = "0" ] || [ "${MAX_PROCS}" = "" ] ; then
    MAX_PROCS=""
  else
    MAX_PROCS="-P ${MAX_PROCS}"
  fi
}

CheckingVariables () {
  if [ "${FILE}" = "" ] ; then
    echo "Error: missing header specification file."
    exit 1
  fi
  if [ ! -f "${FILE}" ] ; then
    echo "Error: header specification file not found: ${FILE}"
    exit 1
  fi
  if [ "${HEADER_SRC}" = ""  ] ; then
    echo "Error: missing header directory."
    exit 1
  fi
  if [ ! -d "${HEADER_SRC}" ] ; then
    echo "Error: header directory not found: ${HEADER_SRC}/"
    exit 1
  fi
  if [ ! -d "${TARGET_DIR}" ] ; then
    echo "Error: target directory not found: ${TARGET_DIR}"
    exit 1
  fi
  if [ ! -f "${HEADACHE_CONFIG}" ] ; then
    echo "Error: headache config file not found: ${HEADACHE_CONFIG}"
    exit 1
  fi
}

PROCESS=""
MAX_PROCS=""
PARALLEL=""
REQUIREMENTS="xargs"
while [ "$1" != "" ] ; do
  case "$1" in
    -h)     Usage;;
    -help)  Usage;;
    --help) Usage;;
    --max-procs)  shift; MAX_PROCS="$1";;
    --dry-run)  PROCESS="echo";;
    --parallel) PARALLEL="parallel"; REQUIREMENTS="${PARALLEL}";;
    *) break;;
  esac
  shift
done

Requires ${HEADACHE} gawk grep tr ${REQUIREMENTS}

SetVariables $@

CheckingVariables

# Checking the format of the input file and extract line number of the error.
grep -v "^#" ${FILE} | \
    gawk -F ":"  '$1=="" || $1~/[^ ] [^ ]/ || $2==""|| $2~/[^ ] [^ ]/ || $3!="" { print "'${FILE}:'" NR ": " $0 ; exit 2 }'
if [ "$?" != "0" ] ; then
  echo "Error: wrong line format." 
  echo "So, nothing is modified." 
  exit 1
fi

# Ok, go on.
if [ "${PARALLEL}" != "" ] ; then

# 'parallel' considers the full line as one argument, so
# 'tr' is used to split the line in two and empty line have to be removed.
  grep -v "^#" $1 \
    | grep -v "\.ignore$" \
    | tr -s ":[:blank:]" "\n" | grep -v '^$' \
    | ${PARALLEL} -n 2 ${MAX_PROCS} ${PROCESS} ${HEADACHE} -c ${HEADACHE_CONFIG} -h ${HEADER_SRC}/{2} ${TARGET_DIR}/{1}
 
else

# 'xargs' has no support for context replace, so 'gawk" is used to create the arguments.
  grep -v "^#" $1 \
    | grep -v "\.ignore$" \
    | tr -s ":[:blank:]" " " | grep -v '^ *$' \
    | gawk '{ print "'${HEADER_SRC}'/" $2 " '${TARGET_DIR}'/" $1 }' \
    | xargs -n 2 ${MAX_PROCS} ${PROCESS} ${HEADACHE} -c ${HEADACHE_CONFIG} -h
 
fi
