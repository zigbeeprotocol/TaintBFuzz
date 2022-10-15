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

"""This script uses blug and a build_commands.json file to produce an
analysis GNUmakefile, as automatically as possible."""

import argparse
import json
import logging
import os
from pathlib import Path
import re
import shutil
import sys
import subprocess

import function_finder
import source_filter

script_dir = os.path.dirname(sys.argv[0])

# Command-line parsing ########################################################

parser = argparse.ArgumentParser(
    description="""Produces a GNUmakefile
for analysis with Frama-C. Tries to use a build_commands.json file if
available."""
)
parser.add_argument(
    "--debug",
    metavar="FILE",
    help="enable debug mode and redirect output to the specified file",
)
parser.add_argument("--force", action="store_true", help="overwrite files without prompting")
parser.add_argument(
    "--jbdb",
    metavar="FILE",
    default="build_commands.json",
    help="path to JBDB (default: build_commands.json)",
)
parser.add_argument(
    "--machdep", metavar="MACHDEP", help="analysis machdep (default: Frama-C's default)"
)
parser.add_argument(
    "--main",
    metavar="FUNCTION",
    default="main",
    help="name of the main function (default: main)",
)
parser.add_argument(
    "--sources",
    metavar="FILE",
    nargs="+",
    help="list of sources to parse (overrides --jbdb)",
    type=Path,
)
parser.add_argument(
    "--targets",
    metavar="FILE",
    nargs="+",
    help="targets to build. When using --sources, " + "only a single target is allowed.",
    type=Path,
)

args = parser.parse_args()
force = args.force
jbdb_path = args.jbdb
machdep = args.machdep
main = args.main
sources = args.sources
targets = args.targets
debug = args.debug

debug_level = logging.DEBUG if debug else logging.INFO
# special values for debug filename
if debug == "stdout":
    logging.basicConfig(stream=sys.stdout, level=debug_level, format="[%(levelname)s] %(message)s")
elif debug == "stderr":
    logging.basicConfig(stream=sys.stderr, level=debug_level, format="[%(levelname)s] %(message)s")
elif debug:
    logging.basicConfig(
        filename=debug,
        level=debug_level,
        filemode="w",
        format="[%(levelname)s] %(message)s",
    )
else:
    logging.basicConfig(level=logging.INFO, format="[%(levelname)s] %(message)s")

dot_framac_dir = Path(".frama-c")

# Check required environment variables and commands in the PATH ###############

framac_bin = os.getenv("FRAMAC_BIN")
if not framac_bin:
    sys.exit("error: FRAMAC_BIN not in environment (set by frama-c-script)")
framac_bin = Path(framac_bin)

under_test = os.getenv("PTESTS_TESTING")

# Prepare blug-related variables and functions ################################

blug = os.getenv("BLUG")
if not blug:
    blug = shutil.which("blug")
    if not blug:
        sys.exit("error: path to 'blug' binary must be in PATH or variable BLUG")
blug = Path(blug)
blug_dir = blug.resolve().parent
# to import blug_jbdb
sys.path.insert(0, blug_dir.as_posix())
import blug_jbdb
from blug_jbdb import prettify


# Auxiliary functions #########################################################


def call_and_get_output(command_and_args):
    try:
        return subprocess.check_output(command_and_args, stderr=subprocess.STDOUT).decode()
    except subprocess.CalledProcessError as e:
        sys.exit(f"error running command: {command_and_args}\n{e}")


def ask_if_overwrite(path):
    yn = input(f"warning: {path} already exists. Overwrite? [y/N] ")
    if yn == "" or not (yn[0] == "Y" or yn[0] == "y"):
        sys.exit("Exiting without overwriting.")


def insert_lines_after(lines, line_pattern, new_lines):
    re_line = re.compile(line_pattern)
    for i, line in enumerate(lines):
        if re_line.search(line):
            for j, new_line in enumerate(new_lines):
                lines.insert(i + 1 + j, new_line)
            return
    sys.exit(f"error: no lines found matching pattern: {line_pattern}")


# delete the first occurrence of [line_pattern]
def delete_line(lines, line_pattern):
    re_line = re.compile(line_pattern)
    for i, line in enumerate(lines):
        if re_line.search(line):
            del lines[i]
            return
    sys.exit(f"error: no lines found matching pattern: {line_pattern}")


def replace_line(lines, line_pattern, value, all_occurrences=False):
    replaced = False
    re_line = re.compile(line_pattern)
    for i, line in enumerate(lines):
        if re_line.search(line):
            lines[i] = value
            replaced = True
            if not all_occurrences:
                return
    if replaced:
        return
    sys.exit(f"error: no lines found matching pattern: {line_pattern}")


# replaces '/' and '.' with '_' so that a valid target name is created
def make_target_name(target):
    return prettify(target).replace("/", "_").replace(".", "_")


# sources are pretty-printed relatively to the .frama-c directory, where the
# GNUmakefile will reside
def rel_prefix(path):
    return path if os.path.isabs(path) else os.path.relpath(path, start=dot_framac_dir)


def pretty_sources(sources):
    return [f"  {rel_prefix(source)} \\" for source in sources]


def lines_of_file(path):
    return path.read_text().splitlines()


fc_stubs_copied = False


def copy_fc_stubs():
    global fc_stubs_copied
    dest = dot_framac_dir / "fc_stubs.c"
    if not fc_stubs_copied:
        fc_stubs = lines_of_file(share_dir / "analysis-scripts" / "fc_stubs.c")
        re_main = re.compile(r"\bmain\b")
        for i, line in enumerate(fc_stubs):
            if line.startswith("//"):
                continue
            fc_stubs[i] = re.sub(re_main, main, line)
        if not force and dest.exists():
            ask_if_overwrite(dest)
        with open(dest, "w") as f:
            f.write("\n".join(fc_stubs))
        logging.info("wrote: %s", dest)
        fc_stubs_copied = True
    return dest


# Returns pairs (line_number, has_args) for each likely definition of
# [funcname] in [filename].
# [has_args] is used to distinguish between main(void) and main(int, char**).
def find_definitions(funcname, filename):
    file_content = source_filter.open_and_filter(filename, not under_test)
    file_lines = file_content.splitlines(keepends=True)
    newlines = function_finder.compute_newline_offsets(file_lines)
    defs = function_finder.find_definitions_and_declarations(
        True, False, filename, file_content, file_lines, newlines, funcname
    )
    res = []
    for d in defs:
        defining_line = file_lines[d[2] - 1]
        after_funcname = defining_line[defining_line.find(funcname) + len(funcname) :]
        # heuristics: if there is a comma after the function name,
        # it is very likely the signature contains arguments;
        # otherwise, the function is either defined in several lines,
        # or we somehow missed it. By default, we assume it has no arguments
        # if we miss it.
        has_args = "," in after_funcname
        res.append((d[2], has_args))
    return res


def list_partition(f, l):
    """Equivalent to OCaml's List.partition: returns 2 lists with the elements of l,
    partitioned according to predicate f."""
    l1 = []
    l2 = []
    for e in l:
        if f(l):
            l1.append(e)
        else:
            l2.append(e)
    return l1, l2


def pp_list(l):
    """Applies prettify to a list of sources/targets and sorts the result."""
    return sorted([prettify(e) for e in l])


# End of auxiliary functions ##################################################

sources_map = dict()
if sources:
    if not targets:
        sys.exit("error: option --targets is mandatory when --sources is specified")
    if len(targets) > 1:
        sys.exit(
            "error: option --targets can only have a single target when --sources is specified"
        )
    sources_map[targets[0]] = sources
elif os.path.isfile(jbdb_path):
    # JBDB exists
    with open(jbdb_path, "r") as data:
        jbdb = json.load(data)
    blug_jbdb.absolutize_jbdb(jbdb)
    filter_source, filter_target = blug_jbdb.get_filters("c-programs")
    # program_targets are those we prefer, and the only ones used in "automatic" mode;
    # non_program_targets are only used if the user specified them in the command line.
    program_targets = []
    non_program_targets = []
    for f in jbdb:
        programs, other_targets = list_partition(filter_target, f["targets"])
        program_targets += programs
        non_program_targets += other_targets
    logging.debug("program_targets: %s", pp_list(program_targets))
    logging.debug("non_program_targets: %s", pp_list(non_program_targets))
    all_jbdb_targets = program_targets + non_program_targets
    if not all_jbdb_targets:
        sys.exit(f"no targets found in JBDB ({jbdb_path})")
    if not targets:
        # no targets specified in command line; use all programs from JBDB
        targets = program_targets
    logging.info("Computing sources for each target (%d target(s))...", len(targets))
    unknown_targets_from_cmdline = []
    graph = blug_jbdb.build_graph(jbdb)
    for target in targets:
        if target not in all_jbdb_targets:
            unknown_targets_from_cmdline.append(target)
            # do not return immediately; we want to report all invalid targets at once
        else:
            if unknown_targets_from_cmdline != []:
                continue  # keep looping to accumulate all invalid targets, but avoid extra work
            sources = blug_jbdb.collect_leaves(graph, [target])
            c_sources, non_c_sources = list_partition(filter_source, sources)
            logging.debug("non_c_sources: %s", pp_list(non_c_sources))
            sources_map[target] = c_sources
    if unknown_targets_from_cmdline:
        targets_pretty = "\n".join(unknown_targets_from_cmdline)
        sys.exit("target(s) not found in JBDB:\n{targets_pretty}")
else:
    if not jbdb_path:
        sys.exit("error: either a JBDB or option --sources are required")
    else:
        sys.exit(f"error: invalid JBDB path: '{jbdb_path}'")

logging.debug(
    "sources_map: %s",
    sorted([prettify(k) + ": " + ", ".join(pp_list(v)) for (k, v) in sources_map.items()]),
)
logging.debug("targets: %s", pp_list(targets))

# check that source files exist
unknown_sources = sorted({s for sources in sources_map.values() for s in sources if not s.exists()})
if unknown_sources:
    sys.exit("error: source(s) not found:\n" + "\n".join(pp_list(unknown_sources)))

# Check that the main function is defined exactly once per target.
# note: this is only based on heuristics (and fails on a few real case studies),
# so we cannot emit errors, only warnings.
# We also need to check if the main function uses a 'main(void)'-style
# signature, to patch fc_stubs.c.

main_definitions = {}
for target, sources in sources_map.items():
    main_definitions[target] = []
    for source in sources:
        fundefs = find_definitions(main, source)
        main_definitions[target] += [(source, fundef[0], fundef[1]) for fundef in fundefs]
    if main_definitions[target] == []:
        logging.warning(
            "function '%s' seems to be never defined in the sources of target '%s'",
            main,
            prettify(target),
        )
    elif len(main_definitions[target]) > 1:
        logging.warning(
            "function '%s' seems to be defined multiple times in the sources of target '%s':",
            main,
            prettify(target),
        )
        for (filename, line, _) in main_definitions[target]:
            print(f"- definition at {filename}:{line}")

# End of checks; start writing GNUmakefile and stubs from templates ###########

if not dot_framac_dir.is_dir():
    logging.debug("creating %s", dot_framac_dir)
    dot_framac_dir.mkdir(parents=True, exist_ok=False)

fc_config = json.loads(call_and_get_output([framac_bin / "frama-c", "-print-config-json"]))
share_dir = Path(fc_config["datadir"])

# copy fc_stubs if at least one main function has arguments
any_has_arguments = False
for defs in main_definitions.values():
    if any(d[2] for d in defs):
        any_has_arguments = True
        break

if any_has_arguments:
    fc_stubs = copy_fc_stubs()
    for target in targets:
        if any(d[2] for d in main_definitions[target]):
            logging.debug(
                "target %s has main with args, adding fc_stubs.c to its sources",
                prettify(target),
            )
            sources_map[target].insert(0, fc_stubs)

gnumakefile = dot_framac_dir / "GNUmakefile"

template = lines_of_file(share_dir / "analysis-scripts" / "template.mk")

if machdep:
    machdeps = fc_config["machdeps"]
    if machdep not in machdeps:
        logging.warning(
            "unknown machdep (%s) not in Frama-C's default machdeps:\n%s",
            machdep,
            " ".join(machdeps),
        )
    replace_line(template, "^MACHDEP = .*", f"MACHDEP = {machdep}")

if jbdb_path:
    insert_lines_after(
        template,
        "^FCFLAGS",
        [f"  -json-compilation-database {rel_prefix(jbdb_path)} \\"],
    )

targets_eva = [f"  {make_target_name(target)}.eva \\" for target in targets]
replace_line(template, "^TARGETS = main.eva", "TARGETS = \\")
insert_lines_after(template, r"^TARGETS = \\", targets_eva)

delete_line(template, r"^main.parse: \\")
delete_line(template, r"^  main.c \\")
for target, sources in reversed(sources_map.items()):
    pp_target = make_target_name(target)
    new_lines = [f"{pp_target}.parse: \\"] + pretty_sources(sources) + [""]
    if any(d[2] for d in main_definitions[target]):
        logging.debug(
            "target %s has main with args, adding -main eva_main to its FCFLAGS",
            prettify(target),
        )
        new_lines += [f"{pp_target}.parse: FCFLAGS += -main eva_main", ""]
    insert_lines_after(template, "^### Each target <t>.eva", new_lines)

gnumakefile.write_text("\n".join(template))

logging.info("wrote: %s", gnumakefile)

# write path.mk, but only if it does not exist.
path_mk = dot_framac_dir / "path.mk"
if not force and path_mk.exists():
    logging.info("%s already exists, will not overwrite it", path_mk)
else:
    path_mk.write_text(
        f"""FRAMAC_BIN={framac_bin}
ifeq ($(wildcard $(FRAMAC_BIN)),)
# Frama-C not installed locally; using the version in the PATH
else
FRAMAC=$(FRAMAC_BIN)/frama-c
FRAMAC_GUI=$(FRAMAC_BIN)/frama-c-gui
endif
"""
    )
    logging.info("wrote: %s", path_mk)
