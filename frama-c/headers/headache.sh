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
Usage() {
  APPLI=$(basename $APPLINAME)
  echo "Usage: $APPLI -c <headache-config> -h <header-file> <file>"
  echo "  Runs headache with the same arguments when <file> exists" 
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

Error() {
  echo "Error: $@"
  exit 1
}

CheckingVariables () {
  ([ "$1" = "--help" ] || [ "$1" = "-help" ]  || [ "$1" = "-h" ]) && Usage
  [ "$6" != "" ]   && Error "too much arguments"
  [ "$5" = "" ]    && Error "too few arguments: $@"
  [ "$1" != "-c" ] && Error "missing -c as first option"
  [ ! -f "$2" ]    && Error "config file not found $2"
  [ "$3" != "-h" ] && Error "missing -h as second option"
  [ ! -f "$4" ]    && Error "header file not found $5"
}

Requires headache
CheckingVariables $@

if [ -f "$5" ]; then
  headache $@
fi
