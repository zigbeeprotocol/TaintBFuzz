#! /bin/sh
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
# Converts a Frama-C plugin from Frama-C 19 Potassium to Frama-C 20 Calcium,
# on a best-efforts basis (no guarantee that the result is fully compatible).
#
# known missing features:
# - doesn't work if a directory name contains spaces
# - doesn't follow symbolic links to directories

ARGS=$@

DIR=

# verbosing on by default
VERBOSE="v"

sedi ()
{
  if [ -n "`sed --help 2> /dev/null | grep \"\\-i\" 2> /dev/null`" ]; then
    sed -i "$@"
  else
      # option '-i' is not recognized by sed: use a tmp file
    new_temp=`mktemp /tmp/frama-c.XXXXXXX` || exit 1
    sed "$@" > $new_temp
    eval last=\${$#}
    mv $new_temp $last
  fi
}

dirs ()
{
  if [ -z "$DIR" ]; then
    DIR=.
  fi
}

safe_goto ()
{
  dir=$1
  cd $dir
  $3
  cd $2
}

goto ()
{
  if [ -d $1 ]; then
    safe_goto $1 $2 $3
  else
    echo "Directory '$1' does not exist. Omitted."
  fi
}

process_file ()
{
  file=$1
  if [ "$VERBOSE" ]; then
    echo "Processing file $file"
  fi
  sedi \
   -e 's/Config\.version/Fc_config.version/g' \
   -e 's/Config\.codename/Fc_config.codename/g' \
   -e 's/Config\.version_and_codename/Fc_config.version_and_codename/g' \
   -e 's/Config\.major_version/Fc_config.major_version/g' \
   -e 's/Config\.minor_version/Fc_config.minor_version/g' \
   -e 's/Config\.is_gui/Fc_config.is_gui/g' \
   -e 's/Config\.ocamlc/Fc_config.ocamlc/g' \
   -e 's/Config\.ocamlopt/Fc_config.ocamlopt/g' \
   -e 's/Config\.ocaml_wflags/Fc_config.ocaml_wflags/g' \
   -e 's/Config\.datadir/Fc_config.datadir/g' \
   -e 's/Config\.datadirs/Fc_config.datadirs/g' \
   -e 's/Config\.framac_libc/Fc_config.framac_libc/g' \
   -e 's/Config\.libdir/Fc_config.libdir/g' \
   -e 's/Config\.plugin_dir/Fc_config.plugin_dir/g' \
   -e 's/Config\.plugin_path/Fc_config.plugin_path/g' \
   -e 's/Config\.compilation_unit_names/Fc_config.compilation_unit_names/g' \
   -e 's/Config\.library_names/Fc_config.library_names/g' \
   -e 's/Config\.preprocessor/Fc_config.preprocessor/g' \
   -e 's/Config\.using_default_cpp/Fc_config.using_default_cpp/g' \
   -e 's/Config\.preprocessor_is_gnu_like/Fc_config.preprocessor_is_gnu_like/g' \
   -e 's/Config\.preprocessor_supported_arch_options/Fc_config.preprocessor_supported_arch_options/g' \
   -e 's/Config\.preprocessor_keep_comments/Fc_config.preprocessor_keep_comments/g' \
   -e 's/Config\.dot/Fc_config.dot/g' \
   $file
}

apply_one_dir ()
{
  if [ "$VERBOSE" ]; then
    echo "Processing directory `pwd`"
  fi
  for f in `ls -p1 *.ml* 2> /dev/null`; do
    process_file $f
  done
}

apply_recursively ()
{
  apply_one_dir
  for d in `ls -p1 | grep \/`; do
    safe_goto $d .. apply_recursively
  done
}

applying_to_list ()
{
  dirs
  tmpdir=`pwd`
  for d in $DIR; do
    goto $d $tmpdir $1
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
  for s in $ARGS; do
    parse_arg $s
  done
  applying_to_list $FN
}

cmd_line
exit 0
