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

# Base dir of this script
BASEDIR="$(realpath `dirname $0`)"

# Check that the E-ACSL changelog does not contain <TAB>
# Note: do not use -P, which is not macOS-compatible
tab_lines_count=$(grep -c -e "$(printf '\t')" $BASEDIR/doc/Changelog)
if [ "$tab_lines_count" -ne "0" ]; then
    echo "Found <TAB> in E-ACSL changelog"
    exit 1
fi

exit 0
