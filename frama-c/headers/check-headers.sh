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
echo $0 $@
Usage() {
  APPLI=$(basename $APPLINAME)
  echo "Usage: $APPLI <options> <files>"
  echo "  $APPLI [--update] --spec-files <spec-files>"
  echo "    1. Checks entries of <spec-files>"
  echo "    --update: updates <spec-files> by removing comments and multiple entries"
  echo "  $APPLI [--update] [--no-headers <header-file>]* <spec-file> ([--files-from] <file>]*"
  echo "    1. Checks entries of <spec-file>"
  echo "    --update: updates <spec-file> by removing comments and multiple entries"
  echo "    2. Checks that every <files> have an entry into the <spec-file>"
  echo "    3. Checks that all the <files> are not attributed to <header-file> in <spec-file>"
  echo "    --no-headers <header-file>: cumulative option"
  exit 0
}

Requires () {
  for File in "$@" 
  do
    where=$(which $File)
    if [ "$?" != "0" ] ; then
      echo "Error: executable not found: $File"
      exit 1
    fi
  done
}

RegExp=""
Checking () {

  Requires sort tr grep diff sed

  if [ "$SpecFilesOpt" != "" ] &&  [ "$HeadersOpt" != "" ] ; then
    echo "Error: given options are exclusives"
    exit 1
  fi

  if [ "$1" = "" ] ; then
    echo "Error: missing argument"
    exit 1
  fi

  if [ ! -f "$1" ] ; then
    echo "Error: file not found: $file"
    exit 1
  fi

  if [ "$SpecFilesOpt" != "" ] ; then
    shift
    for file in $@ ; do
       if [ "$file" != "--files-from" ] && [ ! -f $file ] ; then
          echo "Error: file not found: $file"
        exit 1
       fi
    done
  fi

  if [ "$HeadersOpt" != "" ] ; then
    RegExp="("
    for file in $HeadersOpt ; do
      SyntaxOk=$(echo "$file" | tr -d "._[:alnum:]")
      if [ "$SyntaxOk" != "" ] ; then
        echo "Error: invalid header filename: $file"
        exit 1
      fi
      if [ "$RegExp" != "(" ] ; then
        RegExp="${RegExp}|"
      fi
      RegExp="${RegExp}$(echo $file | sed -e 's:\.:\\.:')"
    done
      RegExp="^${RegExp}):"
  fi
}

Result="0"
Check () {
  Warn=""
  cat $1 \
    | tr "[:blank:]" " " \
    | sed -e 's:  *: :g' \
    | sed -e 's:^ ::g' \
    | sed -e 's: $::g' \
    | sed -e 's/ :/:/g' \
    | sed -e 's/:\([^ ]\)/: \1/g' \
    > $1.$$
  TMP1=$1.$$
  if [ "$?" != "0" ] && [ "$2" = "-step-1" ] ; then
    echo "  Warning: some blank characters can be cleaned:"
    diff $1 $TMP1 | grep "^> "
    Warn="Ok"
  fi
  grep -v "^#" $TMP1 > ${TMP1}.$$
  TMP2=${TMP1}.$$
  LC_ALL=C sort -k2 -k1 $TMP2 > $TMP1
  diff -q $TMP1 $TMP2 > /dev/null
  if [ "$?" != "0" ] && [ "$2" = "-step-1" ] ; then
    echo "  Warning: some entries are unsorted:"
    diff $TMP1 $TMP2 | grep "^> "
    Warn="Ok"
  fi
  LC_ALL=C sort -u -k2 -k1 $TMP1 > $TMP2
  diff -q $TMP2 $TMP1 > /dev/null
  if [ "$?" != "0" ] ; then
    if [ "$2" = "-step-1" ] ; then
      echo "  Warning: some entries are duplicated:"
    else
      echo "  Warning: the following given files are duplicated:"
    fi
    diff $TMP2 $TMP1 | sed -n -e "s/^> ~no-entry-for:/  /p"
    Warn="Ok"
  fi
  LC_ALL=C sort -u -k2 $TMP2 > $TMP1
  if [ "$3" != "" ] ; then
    diff $TMP1 $3 > /dev/null
    if [ "$?" != "0" ] ; then
      echo "  Error: some files have no entry:"
      diff $3 $TMP1 |  sed -n -e "s/^> ~no-entry-for:/  /p"
      Warn="OkOk"
      Result="1"
    fi
  else
    diff -q $TMP1 $TMP2 > /dev/null
    if [ "$?" != "0" ] ; then
      if [ "$2" = "-step-1" ] ; then
        echo "  Error: some entries are duplicated."
        echo "  removed entries:"
      else
        echo "  Error: some checked entries have unwanted headers:"
      fi
      diff $TMP1 $TMP2 | grep "^> "
      Warn="OkOk"
      Result="1"
    fi
  fi
}

CheckSpecFile () {
  echo " Checking specification file $1..."
  Check "$1" "-step-1"
  if [ "$Warn" = "OkOk" ] ; then
    if [ "$UpdateOpt" != "--update" ] ; then
      rm $TMP1 $TMP2 
      echo " Use --update option to update $1 file"
      exit 1
    fi
  fi
  if [ "$UpdateOpt" = "--update" ] ; then
    if [ "$Warn" = "" ] ; then
      diff -q $TMP1 $1 > /dev/null
      if [ "$?" != "0" ] ; then
         Warn="Ok"
      fi
    fi
    if [ "$Warn" = "" ] ; then
       echo "Warning: already up to date"
    else
       echo " Updating file $1"
       mv $TMP1 $1
    fi
  fi
}

UpdateOpt=""
HeadersOpt=""
SpecFilesOpt=""
while [ "$1" != "" ] ; do
  case "$1" in
    -h)     Usage;;
    -help)  Usage;;
    --help) Usage;;
    --update) UpdateOpt="$1";;
    --spec-files) SpecFilesOpt="$1";;
    --no-headers) shift; HeadersOpt="${Headers} $1";;
    --files-from) break;;
    --*) echo "Unknown option $1"; exit 1;;
    *) break;;
  esac
  shift
done

Checking $@

BuildTmpFile() {
  TmpFile="$1"
  shift
  Str="$1"
  shift
  while [ "$1" != "" ]; do
    if [ "$1" = "--files-from" ] ; then
      shift
      cat $1 \
        | tr "[:blank:]" " " \
        | sed -e 's:  *: :g' \
        | sed -e 's:^ ::g' \
        | sed -e 's: $::g' \
        | egrep -v '^#' \
        | sed -e "s#^#${Str}: #" >> $TMP
      else
        echo "${Str}: $1" >> $TMP
      fi
    shift
  done
}

if [ "$SpecFilesOpt" = "" ] ; then
#  echo "Step 1..."
  SpecFile=$1
  shift
  CheckSpecFile $SpecFile
#  echo " Removing temporary files"
  mv $TMP2 $TMP1
  RefStep2=$TMP1

  if [ "$1" != "" ]; then
#    echo "Step 2..."
    echo " Checking that all given files have an entry..."
    cat $RefStep2 > $RefStep2.$$
    TMP=$RefStep2.$$
    BuildTmpFile $TMP "~no-entry-for" $@
    Check $TMP "-step-2" $RefStep2
#    echo " Removing temporary files"
    rm -f $TMP $TMP1 $TMP2 
  fi
  rm -f $RefStep2

  if [ "$RegExp" != "" ] && [ "$1" != "" ]; then
#    echo "Step 3..."
    echo " Checking for files having unwanted headers..." 
    egrep -e "$RegExp" $SpecFile > $SpecFile.$$
    TMP=$SpecFile.$$
    BuildTmpFile $TMP "./looking-for" $@
    Check $TMP "-step-3"
#    echo " Removing temporary files"
    rm -f $TMP $TMP1 $TMP2 
  fi

  if test $Result -eq 0; then
    echo "No issue detected. Great!"
  fi
  exit $Result

else
#  echo "Step 1..."
  for file in $@ ; do
    CheckSpecFile $file
#    echo " Removing temporary files"
    rm -f $TMP1 $TMP2 
  done
fi