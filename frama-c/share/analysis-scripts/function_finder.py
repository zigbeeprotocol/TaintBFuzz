# -*- coding: utf-8 -*-
##########################################################################
#                                                                        #
#  This file is part of Frama-C.                                         #
#                                                                        #
#  Copyright (C) 2007-2021                                               #
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

"""Exports find_function_in_file, to be used by other scripts"""

import bisect
import os
import re

# To minimize the amount of false positives, we try to match the following:
# - the line must begin with a C identifier (declarations and definitions in C
#   rarely start with spaces in the line), or with the function name itself
#   (supposing the return type is in the previous line)
# - any number of identifiers are allowed (to allow for 'struct', 'volatile',
#   'extern', etc)
# - asterisks are allowed both before and after identifiers, except for the
#   first one (to allow for 'char *', 'struct **ptr', etc)
# - identifiers are allowed after the parentheses, to allow for some macros/
#   modifiers

# auxiliary regexes
c_identifier = "[a-zA-Z_][a-zA-Z0-9_]*"
c_id_maybe_pointer = c_identifier + "[*]*"
optional_c_id = "(?:" + c_identifier + ")?"
non_empty_whitespace = r"[ \t\r\n]+"  # includes newline/CR
whitespace = "[ \t\r\n]*"  # includes newline/CR
type_prefix = (
    c_id_maybe_pointer + r"(?:\s+[*]*" + c_id_maybe_pointer + ")*" + non_empty_whitespace + "[*]*"
)
optional_type_prefix = "(?:" + type_prefix + whitespace + ")?"
argument_list = r"\([^)]*\)"

debug = os.getenv("DEBUG", False)

# Precomputes the regex for 'fname'
def prepare_re_specific_name(fname):
    re_fun = re.compile(
        "^"
        + optional_type_prefix
        + fname
        + whitespace
        + argument_list
        + whitespace
        + optional_c_id
        + whitespace
        + "(;|{)",
        flags=re.DOTALL | re.MULTILINE,
    )
    return re_fun


# Returns 0 if not found, 1 if declaration, 2 if definition
def find_specific_name(prepared_re, f):
    with open(f, encoding="ascii", errors="ignore") as data:
        file_content = data.read()
        has_decl_or_def = prepared_re.search(file_content)
        if has_decl_or_def is None:
            return 0
        else:
            is_decl = has_decl_or_def.group(1) == ";"
            return 1 if is_decl else 2


# matches function definitions or declarations
# if funcname is not None, only matches for the specified
# function name
def compute_re_def_or_decl(funcname):
    ident = funcname if funcname else c_identifier
    return re.compile(
        "^"
        + optional_type_prefix
        + "("
        + ident
        + ")"
        + whitespace
        + argument_list
        + whitespace
        + optional_c_id
        + whitespace
        + "(;|{)",
        flags=re.DOTALL | re.MULTILINE,
    )


# matches function calls
re_funcall = re.compile("(" + c_identifier + ")" + whitespace + r"\(")

# Computes the offset (in bytes) of each '\n' in the file,
# returning them as a list
def compute_newline_offsets(file_lines):
    offsets = []
    current = 0
    for line in file_lines:
        current += len(line)
        offsets.append(current)
    return offsets


# Returns the line number (starting at 1) containing the character
# of offset [offset].
# [offsets] is the sorted list of offsets for newline characters in the file.
def line_of_offset(offsets, offset):
    return bisect.bisect_right(offsets, offset) + 1


# Returns the line number (starting at 1) of each line starting with '}'
# as its first character.
#
# This is a heuristic to attempt to detect function closing braces:
# it assumes that the first '}' (without preceding whitespace) after a
# function definition denotes its closing brace.
def compute_closing_braces(file_lines):
    braces = []
    for i, line in enumerate(file_lines, start=1):
        # note: lines contain '\n', so they are never empty
        if line[0] == "}":
            braces.append(i)
    # Special heuristics: if the last line contains whitespace + '}',
    # assume it closes a function.
    last_line_number = len(file_lines) + 1
    if file_lines != [] and last_line_number not in braces:
        last_line = file_lines[-1].lstrip()
        if len(last_line) >= 1 and last_line[0] == "}":
            braces.append(last_line_number)
    return braces


# Returns the first element of [line_numbers] greater than [n], or [None]
# if all numbers are smaller than [n] (this may happen e.g. when no
# closing braces were found).
#
# [line_numbers] must be sorted in ascending order.
def get_first_line_after(line_numbers, n):
    try:
        return line_numbers[bisect.bisect_left(line_numbers, n)]
    except IndexError:
        # could not find line (e.g. for closing braces); return None
        return None


# Returns a list of tuples (fname, is_def, line_start, line_end, terminator_offset)
# for each function definition or declaration.
# If [want_defs] is True, definitions are included.
# If [want_decls] is True, declarations are included.
# [terminator_offset] is the byte offset of the `{` or `;`.
# The list is sorted w.r.t. line numbers (in ascending order).
#
# [terminator_offset] is used by the caller to filter the function prototype
# itself and avoid considering it as a call. For function definitions,
# this is the opening brace; for function declarations, this is the semicolon.
def find_definitions_and_declarations(
    want_defs, want_decls, filename, file_content, file_lines, newlines, funcname=None
):
    braces = compute_closing_braces(file_lines)
    res = []
    re_fundef_or_decl = compute_re_def_or_decl(funcname)
    for match in re.finditer(re_fundef_or_decl, file_content):
        funcname = match.group(1)
        terminator = match.group(2)
        terminator_offset = match.start(2)
        is_def = terminator == "{"
        is_decl = terminator == ";"
        assert is_def or is_decl
        start = line_of_offset(newlines, match.start(1))
        if is_decl:
            if not want_decls:
                continue
            end = line_of_offset(newlines, terminator_offset)
        else:
            if not want_defs:
                continue
            definition = file_content[match.start(1) : newlines[start - 1]]
            # try "single-line function heuristic":
            # assume the function is defined as 'type f(...) { code; }',
            # in a single line
            if definition.strip().endswith("}"):
                end = line_of_offset(newlines, terminator_offset)
            else:
                end = get_first_line_after(braces, start)
                if not end:
                    # no closing braces found; try again the "single-line function heuristic"
                    line_of_opening_brace = line_of_offset(newlines, terminator_offset)
                    if start == line_of_opening_brace and definition.rstrip()[-1] == "}":
                        # assume the '}' is closing the '{' from the same line
                        end = line_of_opening_brace
                    else:
                        # no opening brace; assume a false positive and skip definition
                        print(
                            f"{os.path.relpath(filename)}:{start}:closing brace not found, "
                            f"skipping potential definition of '{funcname}'"
                        )
                        continue
        if debug:
            print(
                f"function_finder: {'def' if is_def else 'decl'} of "
                f"{funcname} between {start} and {end}"
            )
        res.append((funcname, is_def, start, end, terminator_offset))
    return res


# list of identifiers which are never function calls
calls_blacklist = ["if", "while", "for", "return", "sizeof", "switch", "_Alignas"]

# Returns a list of tuples (fname, line, offset) for each function call.
#
# Note: this may include the function prototype itself;
# it must be filtered by the caller.
def find_calls(file_content, newlines):
    # create a list of Match objects that fit "pattern" regex
    res = []
    for match in re.finditer(re_funcall, file_content):
        funcname = match.group(1)
        offset = match.start(1)
        line = line_of_offset(newlines, offset)
        if funcname not in calls_blacklist:
            res.append((funcname, line, offset))
    return res


# Returns the caller of [call], that is, the function whose definition
# contains the line where [call] happens.
# Returns [None] if there is no function at such line (i.e. a false positive).
#
# [defs] must be sorted in ascending order.
def find_caller(defs, call):
    (_called, line, offset) = call
    for (fname, _is_def, start, end, brace_offset) in defs:
        if start <= line <= end and offset > brace_offset:
            return fname
        elif start > line:
            return None
    return None
