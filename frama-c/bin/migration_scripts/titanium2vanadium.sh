#!/bin/bash
##########################################################################
#                                                                        #
#  This file is part of Frama-C.                                         #
#                                                                        #
#  Copyright (C) 2007-2022                                               #
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

#
# Converts a Frama-C plugin from Frama-C 22 Titanium to Frama-C 23 Vanadium,
# on a best-efforts basis (no guarantee that the result is fully compatible).
#
# known missing features:
# - doesn't follow symbolic links to directories

DIR=

# verbose on by default
VERBOSE="v"

# test once if sed supports -i (BSD/macOS does not)
SED_HAS_I=$(sed --help 2>/dev/null | grep '\-i' 2>/dev/null)

# [sedi file expressions] runs 'sed -i expressions' on the specified file;
# if '-i' is not supported, creates a temporary file and overwrites the
# original, like '-i' does.
sedi ()
{
  file="$1"
  shift
  if [ -n "$SED_HAS_I" ]; then
    sed -i "$@" "$file"
  else
    # option '-i' is not recognized by sed: use a tmp file
    new_temp=`mktemp /tmp/frama-c.XXXXXXX` || exit 1
    sed "$@" "$file" > "$new_temp"
    mv -f "$new_temp" "$file"
  fi
}

dirs ()
{
  if [ -z "$DIR" ]; then
    DIR=.
  fi
}

# [safe_goto d1 d2 cmd] goes to d1, runs cmd, and returns to d2
safe_goto ()
{
  dir="$1"
  cd "$dir"
  $3
  cd "$2"
}

goto ()
{
  if [ -d "$1" ]; then
    safe_goto "$1" "$2" "$3"
  else
    echo "Directory '$1' does not exist. Omitted."
  fi
}

process_file ()
{
  file="$1"
  if [ "$VERBOSE" ]; then
    echo "Processing file $file"
  fi
  sedi "$file" \
   -e 's/Cil\.Frama_c_builtins/Cil_builtins.Frama_c_builtins/g' \
   -e 's/Cil\.is_builtin/Cil_builtins.is_builtin/g' \
   -e 's/Cil\.is_unused_builtin/Cil_builtins.is_unused_builtin/g' \
   -e 's/Cil\.is_special_builtin/Cil_builtins.is_special_builtin/g' \
   -e 's/Cil\.add_special_builtin/Cil_builtins.add_special_builtin/g' \
   -e 's/Cil\.add_special_builtin_family/Cil_builtins.add_special_builtin_family/g' \
   -e 's/Cil\.init_builtins/Cil_builtins.init_builtins/g' \
   -e 's/Cil\.Builtin_functions/Cil_builtins.Builtin_functions/g' \
   -e 's/Cil\.builtinLoc/Cil_builtins.builtinLoc/g' \
   -e 's/Extlib\.list_of_opt/Option.to_list/g' \
   -e 's/Extlib\.opt_conv /Option.value ~default:/g' \
   -e 's/Extlib\.may_map ~dft:\([^ ]*\) /Option.fold ~none:\1 ~some:/g' \
   -e 's/Extlib\.may_map /Option.fold ~some:/g' \
   -e 's/~dft:/~none:/g' \
   -e 's/Extlib\.may /Option.iter /g' \
   -e 's/Extlib\.opt_map/Option.map/g' \
   -e 's/Extlib\.has_some/Option.is_some/g' \
   -e 's/Extlib\.opt_bind/Option.bind/g' \
   -e 's/Extlib\.the \([^~]\)/Option.get \1/g' \
   -e 's/Extlib\.opt_equal/Option.equal/g' \
   -e 's/Extlib\.opt_compare/Option.compare/g' \
   -e 's/Extlib\.array_exists/Array.exists/g' \
   -e 's/Filepath\.Normalized\.is_unknown/Filepath.Normalized.is_empty/g' \
   -e 's/Filepath\.Normalized\.unknown/Filepath.Normalized.empty/g'
}

apply_one_dir ()
{
  if [ "$VERBOSE" ]; then
    echo "Processing directory `pwd`"
  fi
  for f in $(find . -maxdepth 1 -type f -name "*.ml*" 2> /dev/null); do
    process_file "$f"
  done
}

apply_recursively ()
{
    apply_one_dir
    while IFS= read -r -d $'\0' d; do
        if [ "$d" = "." ]; then
            continue
        fi
        safe_goto "$d" .. apply_recursively
    done < <(find . -maxdepth 1 -type d -print0)
}

applying_to_list ()
{
  dirs
  tmpdir=`pwd`
  for d in $DIR; do
    goto "$d" "$tmpdir" "$1"
  done
}

help ()
{
  echo "Usage: $0 [options | directories]

Options are:
  -r | --recursive       Check subdirectories recursively
  -h | --help            Display help message
  -q | --quiet           Quiet mode (i.e. non-verbose mode)
  -v | --verbose         Verbose mode (default)"
  exit 0
}

error ()
{
  echo "$1.
Do \"$0 -h\" for help."
  exit 1
}

FN="apply_one_dir"

parse_arg ()
{
  case $1 in
    -r | --recursive)     FN="apply_recursively";;
    -h | -help      )     help; exit 0;;
    -q | --quiet    )     VERBOSE=;;
    -v | --verbose  )     VERBOSE="v";;
    -* )                  error "Invalid option $1";;
    * )                   DIR="$DIR $1";;
  esac
}

cmd_line ()
{
  for s in "$@"; do
    parse_arg "$s"
  done
  applying_to_list $FN
}

cmd_line "$@"
exit 0
