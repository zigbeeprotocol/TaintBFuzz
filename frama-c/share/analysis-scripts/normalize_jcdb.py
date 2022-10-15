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

"""This script removes absolute path references in a JSON Compilation Database."""

# See: http://clang.llvm.org/docs/JSONCompilationDatabase.html

import sys
import os
import json
from pathlib import Path

if len(sys.argv) < 2:
    # no argument, assume default name
    arg = Path("compile_commands.json")
else:
    arg = Path(sys.argv[1])

if not arg.exists():
    print(f"error: file '{arg}' not found")
    sys.exit(f"usage: {sys.argv[0]} [compile_commands.json]")

with open(arg) as data:
    jcdb_json = json.load(data)
jcdb_dir = arg.parent
out_json = {}

replacements = set()

nb_diffs = 0
for entry in jcdb_json:
    if "file" in entry and os.path.isabs(entry["file"]):
        old_entry = entry["file"]
        entry["file"] = os.path.relpath(entry["file"], jcdb_dir)
        if old_entry != entry["file"]:
            nb_diffs += 1
            replacements.add(f"{old_entry} -> {entry['file']}")
        else:
            print(f"warning: absolute path could not be normalized: {entry['file']}")
    elif "directory" in entry and os.path.isabs(entry["directory"]):
        old_entry = entry["directory"]
        entry["directory"] = os.path.relpath(entry["directory"], jcdb_dir)
        if old_entry != entry["directory"]:
            nb_diffs += 1
            replacements.add(f"{old_entry} -> {entry['directory']}")
        else:
            print(f"warning: absolute path could not be normalized: {entry['directory']}")

if nb_diffs == 0:
    print(f"No changes to be applied to {arg}")
else:
    replacements_str = "\n".join(sorted(replacements))
    print(f"Replacements to be made:\n{replacements_str}")
    yn = input(f"{nb_diffs} replacements to be applied. Normalize {arg}? [y/N] ")
    if yn.lower() == "y":
        with open(arg, "w", encoding="utf-8") as outfile:
            json.dump(jcdb_json, outfile, ensure_ascii=False, indent=4)
            print(f"Normalization applied to {arg}")
    else:
        print("Exiting without overwriting.")
