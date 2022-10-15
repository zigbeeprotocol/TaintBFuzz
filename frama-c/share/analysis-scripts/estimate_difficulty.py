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

"""This script uses several heuristics to try and estimate the difficulty
of analyzing a new code base with Frama-C."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile

import build_callgraph
import source_filter

# TODO : avoid relativizing paths when introducing too many ".." ;
# TODO : accept directory as argument (--full-tree), and then do glob **/*.{c,i} inside
# TODO : try to check the presence of compiler builtins
# TODO : try to check for pragmas
# TODO : detect absence of 'main' function (library)

parser = argparse.ArgumentParser(
    description="""
Estimates the difficulty of analyzing a given code base"""
)
parser.add_argument(
    "--header-dirs",
    "-d",
    metavar="DIR",
    nargs="+",
    help="directories containing headers (default: .frama-c)",
)
parser.add_argument("files", nargs="+", help="source files")
args = vars(parser.parse_args())

header_dirs = args["header_dirs"]
if not header_dirs:
    header_dirs = []
files = args["files"]

under_test = os.getenv("PTESTS_TESTING")

# gather information from several sources


def extract_keys(l):
    return [list(key.keys())[0] for key in l]


def get_framac_libc_function_statuses(framac, framac_share):
    if framac:
        (_handler, metrics_tmpfile) = tempfile.mkstemp(prefix="fc_script_est_diff", suffix=".json")
        if debug:
            print("metrics_tmpfile: %s", metrics_tmpfile)
        fc_runtime = framac_share / "libc" / "__fc_runtime.c"
        fc_libc_headers = framac_share / "libc" / "__fc_libc.h"
        subprocess.run(
            [
                framac,
                "-no-autoload-plugins",
                fc_runtime,
                fc_libc_headers,
                "-load-module",
                "metrics",
                "-metrics",
                "-metrics-libc",
                "-metrics-output",
                metrics_tmpfile,
            ],
            stdout=subprocess.DEVNULL,
            check=True,
        )
        with open(metrics_tmpfile) as f:
            metrics_json = json.load(f)
        os.remove(metrics_tmpfile)
    else:
        with open(framac_share / "libc_metrics.json") as f:
            metrics_json = json.load(f)
    defined = extract_keys(metrics_json["defined-functions"])
    spec_only = extract_keys(metrics_json["specified-only-functions"])
    return (defined, spec_only)


re_include = re.compile(r'\s*#\s*include\s*("|<)([^">]+)("|>)')


def grep_includes_in_file(filename):
    file_content = source_filter.open_and_filter(filename, not under_test)
    i = 0
    for line in file_content.splitlines():
        i += 1
        m = re_include.match(line)
        if m:
            kind = m.group(1)
            header = m.group(2)
            yield (i, kind, header)


def get_includes(files):
    quote_includes = {}
    chevron_includes = {}
    for filename in files:
        for line, kind, header in grep_includes_in_file(filename):
            if kind == "<":
                includes = chevron_includes[header] if header in chevron_includes else []
            else:
                includes = quote_includes[header] if header in quote_includes else []
            includes.append((filename, line))
            if kind == "<":
                chevron_includes[header] = includes
            else:
                quote_includes[header] = includes
    return chevron_includes, quote_includes


debug = os.getenv("DEBUG")
verbose = False

framac_bin = os.getenv("FRAMAC_BIN")
if not framac_bin:
    print(
        "Running script in no-Frama-C mode (set FRAMAC_BIN to the directory containing frama-c if you want to use it)."
    )
    framac = None
    script_dir = os.path.dirname(os.path.realpath(__file__))
    framac_share = Path(script_dir) / "share"
else:
    framac = Path(framac_bin) / "frama-c"
    framac_share = Path(
        subprocess.check_output([framac, "-no-autoload-plugins", "-print-share-path"]).decode()
    )

print("Building callgraph...")
cg = build_callgraph.compute(files)

print("Computing data about libc/POSIX functions...")
libc_defined_functions, libc_specified_functions = get_framac_libc_function_statuses(
    framac, framac_share
)

with open(framac_share / "compliance" / "c11_functions.json", encoding="utf-8") as f:
    c11_functions = json.load(f)["data"]

with open(framac_share / "compliance" / "c11_headers.json", encoding="utf-8") as f:
    c11_headers = json.load(f)["data"]

with open(framac_share / "compliance" / "posix_identifiers.json", encoding="utf-8") as f:
    all_data = json.load(f)
    posix_identifiers = all_data["data"]
    posix_headers = all_data["headers"]

recursive_cycles = []
reported_recursive_pairs = set()
build_callgraph.compute_recursive_cycles(cg, recursive_cycles)
for (cycle_start_loc, cycle) in recursive_cycles:
    # Note: in larger code bases, many cycles are reported for the same final
    # function (e.g. for the calls 'g -> g', we may have 'f -> g -> g',
    # 'h -> g -> g', etc; to minimize this, we print just the first one.
    # This does not prevent 3-cycle repetitions, such as 'f -> g -> f',
    # but these are less common.
    if cycle[-1] in reported_recursive_pairs:
        continue
    reported_recursive_pairs.add(cycle[-1])
    (filename, line) = cycle_start_loc
    (x, y) = cycle[0]
    pretty_cycle = f"{x} -> {y}"
    for (x, y) in cycle[1:]:
        pretty_cycle += f" -> {y}"
    print(f"[recursion] found recursive cycle near {filename}:{line}: {pretty_cycle}")

callees = [callee for (_, callee) in list(cg.edges.keys())]
callees = set(callees)
used_headers = set()
print(f"Estimating difficulty for {len(callees)} function calls...")
warnings = 0

for callee in sorted(callees):

    def callee_status(status, standard, reason):
        global warnings
        if status == "warning":
            warnings += 1
        if verbose or debug or status == "warning":
            print(f"- {status}: {callee} ({standard}) {reason}")

    try:
        is_problematic = posix_identifiers[callee]["notes"]["fc-support"] == "problematic"
    except KeyError:
        is_problematic = False
    if callee in posix_identifiers:
        used_headers.add(posix_identifiers[callee]["header"])
    status_emitted = False  # to avoid re-emitting a message for functions in both C11 and POSIX
    if callee in c11_functions:
        standard = "C11"
        # check that the callee is not a macro or type (e.g. va_arg);
        # a few functions, such as strcpy_s, are in C11 but not in POSIX,
        # so we must test membership before checking the POSIX type
        if callee in posix_identifiers and posix_identifiers[callee]["id_type"] != "function":
            continue
        if (not is_problematic) and callee in libc_specified_functions:
            callee_status("good", standard, "is specified in Frama-C's libc")
            status_emitted = True
        elif (not is_problematic) and callee in libc_defined_functions:
            callee_status("ok", standard, "is defined in Frama-C's libc")
            status_emitted = True
        else:
            if callee not in posix_identifiers:
                callee_status("warning", standard, "has neither code nor spec in Frama-C's libc")
                status_emitted = True
    if not status_emitted and callee in posix_identifiers:
        standard = "POSIX"
        # check that the callee is not a macro or type (e.g. va_arg)
        if posix_identifiers[callee]["id_type"] != "function":
            continue
        if (not is_problematic) and callee in libc_specified_functions:
            callee_status("good", standard, "specified in Frama-C's libc")
            status_emitted = True
        elif (not is_problematic) and callee in libc_defined_functions:
            callee_status("ok", standard, "defined in Frama-C's libc")
            status_emitted = True
        else:
            # Some functions without specification are actually variadic
            # (and possibly handled by the Variadic plug-in)
            if "notes" in posix_identifiers[callee]:
                if "variadic-plugin" in posix_identifiers[callee]["notes"]:
                    callee_status("ok", standard, "is handled by the Variadic plug-in")
                    status_emitted = True
                elif is_problematic:
                    callee_status(
                        "warning",
                        standard,
                        "is known to be problematic for code analysis",
                    )
                    status_emitted = True
            if not status_emitted:
                callee_status("warning", standard, "has neither code nor spec in Frama-C's libc")

print(f"Function-related warnings: {warnings}")

if (verbose or debug) and used_headers:
    print("used headers:")
    for header in sorted(used_headers):
        print(f"  <{header}>")

(chevron_includes, quote_includes) = get_includes(files)


def is_local_header(header_dirs, header):
    for d in header_dirs:
        path = Path(d)
        if Path(path / header).exists():
            return True
    return False


print(f"Estimating difficulty for {len(chevron_includes)} '#include <header>' directives...")
non_posix_headers = []
header_warnings = 0
for header in sorted(chevron_includes, key=str.casefold):
    if header in posix_headers:
        fc_support = posix_headers[header]["fc-support"]
        if fc_support == "unsupported":
            header_warnings += 1
            print(f"- WARNING: included header <{header}> is explicitly unsupported by Frama-C")
        else:
            if verbose or debug:
                c11_or_posix = "C11" if header in c11_headers else "POSIX"
                print(f"- note: included {c11_or_posix} header ")
    else:
        if is_local_header(header_dirs, header):
            if verbose or debug:
                print(f"- ok: included header <{header}> seems to be available locally")
        else:
            non_posix_headers.append(header)
            header_warnings += 1
            print(f"- warning: included non-POSIX header <{header}>")
print(f"Header-related warnings: {header_warnings}")


# dynamic allocation

dynalloc_functions = set(["malloc", "calloc", "free", "realloc", "alloca", "mmap"])
dyncallees = dynalloc_functions.intersection(callees)
if dyncallees:
    print(f"- note: calls to dynamic allocation functions: {', '.join(sorted(dyncallees))}")


# unsupported C11-specific features

c11_unsupported = [
    "_Alignas",
    "_Alignof",
    "_Complex",
    "_Generic",
    "_Imaginary",
    "alignas",
    "alignof",  # stdalign.h may use these symbols
]

for keyword in c11_unsupported:
    out = subprocess.Popen(
        ["grep", "-n", "\\b" + keyword + "\\b"] + files + ["/dev/null"],
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    lines = out.communicate()[0].decode("utf-8").splitlines()
    if lines:
        n = len(lines)
        print(
            f"- warning: found {n} line{'s' if n > 1 else ''} with occurrences of "
            f"unsupported C11 construct '{keyword}'"
        )

# assembly code

if "asm" in callees or "__asm" in callees or "__asm__" in callees:
    print("- warning: code seems to contain inline assembly ('asm(...)')")
