#!/usr/bin/env python3
# -*- coding: utf-8 -*-
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

"""This script finds files containing likely declarations and definitions
for a given function name, via heuristic syntactic matching."""

import sys
import build_callgraph

dotfile = None
args = sys.argv[1:]
if "--dot" in args:
    dotarg = args.index("--dot")
    dotfile = args[dotarg + 1]
    args_before = args[: dotarg - 1] if dotarg > 0 else []
    args_after = args[dotarg + 2 :]
    args = args_before + args_after
if not args:
    sys.exit(
        f"""\
usage: {sys.argv[0]} [--dot outfile] file1 file2 ...
prints a heuristic callgraph for the specified files.
If --dot is specified, print in DOT (Graphviz) format
to file outfile, or to stdout if outfile is '-'."""
    )

cg = build_callgraph.compute(args)
if dotfile:
    if dotfile == "-":
        out = sys.stdout
    else:
        out = open(dotfile, "w")
    build_callgraph.print_cg_dot(cg, out)
    if dotfile != "-":
        out.close()
        print(f"wrote {dotfile}")
else:
    build_callgraph.print_cg(cg)
