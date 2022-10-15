##########################################################################
#                                                                        #
#  This file is part of WP plug-in of Frama-C.                           #
#                                                                        #
#  Copyright (C) 2007-2022                                               #
#    CEA (Commissariat a l'energie atomique et aux energies              #
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

m4_define([plugin_file],Makefile.in)

m4_define([FRAMAC_SHARE_ENV],
          [m4_normalize(m4_esyscmd([echo $FRAMAC_SHARE]))])

m4_define([FRAMAC_SHARE],
	  [m4_ifval(FRAMAC_SHARE_ENV,[FRAMAC_SHARE_ENV],
                                     [m4_esyscmd(frama-c -print-path)])])

m4_ifndef([FRAMAC_M4_MACROS],
         [m4_include(FRAMAC_SHARE/configure.ac)]
        )

check_plugin(wp,PLUGIN_RELATIVE_PATH(plugin_file),[WP plug-in],yes,yes)

plugin_require(wp,qed)
plugin_require(wp,rtegen)
plugin_use(wp,gui)

# Why3 API dependency
######################

configure_pkg(why3,[package why3 not found])

plugin_require_pkg(wp,why3)

check_plugin_dependencies

if test "$HAS_OCAML_WHY3" = "yes"; then
AC_MSG_CHECKING(why3 version)
WHY3VERSION=`ocamlfind query -format %v why3 | tr -d '\\r\\n'`
case $WHY3VERSION in
      "")
        AC_MSG_RESULT([not found!])
        plugin_disable(wp,[why3 not found])
        ;;
      0.* | 1.[[01234]].*)
        AC_MSG_RESULT([found $WHY3VERSION: requires 1.5.0+])
        plugin_disable(wp,[non-supported why3 $WHY3VERSION])
        ;;
      1.5.*)
        AC_MSG_RESULT([found $WHY3VERSION: ok])
        ;;
      *)
        AC_MSG_RESULT([found $WHY3VERSION: might work (should be 1.5.0+)])
        ;;
esac
fi

write_plugin_config(Makefile)
