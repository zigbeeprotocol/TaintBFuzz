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

MYDIR=$(dirname $0)
BINDIR=$(cd $MYDIR && pwd) #more portable realpath
ROOTDIR=$BINDIR/..

export FRAMAC_PLUGIN_GUI="$ROOTDIR/lib/plugins/gui"
export FRAMAC_LIB="$ROOTDIR/lib/fc"
export FRAMAC_PLUGIN="$ROOTDIR/lib/plugins"
export FRAMAC_SHARE="$ROOTDIR/share"
