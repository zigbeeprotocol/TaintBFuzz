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

import argparse
import os
import re
import sys
from pathlib import Path

import function_finder

parser = argparse.ArgumentParser(
    description="""
Looks for likely declarations/definitions of a function
in files with extensions '.c', '.h' and '.i'.
If any directories are specified, looks inside them,
otherwise looks inside PWD and /usr/include.
Subdirectories are always considered recursively."""
)

parser.add_argument(
    "--directory",
    "-C",
    metavar="DIR",
    default=".",
    nargs=1,
    help="print paths relative to directory DIR (default: .)",
)
parser.add_argument("funcname", help="function name to search")
parser.add_argument(
    "dir",
    nargs="*",
    type=Path,
    help="directories where to search (if empty: PWD /usr/include)",
)
args = vars(parser.parse_args())

reldir = args["directory"][0]
fname = args["funcname"]
dirs = args["dir"]

if re.match("[a-zA-Z_][a-zA-Z0-9_]*$", fname) is None:
    print("error: function name contains invalid characters: %s" % fname)
    print("       (only letters/digits/underscore allowed)")
    sys.exit(1)

dirs = set(dirs)
if not dirs:
    pwd = os.getcwd()
    dirs = [Path(pwd), Path("/usr/include")]
else:
    dirs = [Path(p) for p in set(sys.argv[2:])]

files = set()
for d in dirs:
    # The usage of Path.glob here prevents symbolic links from being
    # followed, which is desirable in some situations. However, if you
    # need them, try using glob.glob instead.
    files.update(d.glob("**/*.[ich]"))

print("Looking for '%s' inside %d file(s)..." % (fname, len(files)))

possible_declarators = []
possible_definers = []
re_fun = function_finder.prepare_re_specific_name(fname)
for f in files:
    try:
        found = function_finder.find_specific_name(re_fun, f)
        if found:
            if found == 1:
                possible_declarators.append(f)
            else:
                possible_definers.append(f)
    except OSError as e:
        print(f"error opening '{f}' ({e.errno}, {e.strerror}), skipping file")


def relative_path_to(start):
    return lambda p: os.path.relpath(p, start=start)


if not possible_declarators and not possible_definers:
    print("No declaration/definition found for function '%s'" % fname)
    sys.exit(0)

if reldir != ".":
    reldir_msg = f" (relative to '{reldir}')"
else:
    reldir_msg = ""
relative_path = relative_path_to(reldir)
if possible_declarators:
    print(f"Possible declarations for function '{fname}' in the following file(s){reldir_msg}:")
    print(
        "  "
        + "\n  ".join(
            sorted([os.path.relpath(path, start=reldir) for path in possible_declarators])
        )
    )
if possible_definers:
    print(f"Possible definitions for function '{fname}' in the following file(s){reldir_msg}:")
    print(
        "  "
        + "\n  ".join(sorted([os.path.relpath(path, start=reldir) for path in possible_definers]))
    )
