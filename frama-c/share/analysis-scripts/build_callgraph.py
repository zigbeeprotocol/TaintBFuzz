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

import os
import sys

import function_finder
import source_filter

under_test = os.getenv("PTESTS_TESTING")

debug = os.getenv("DEBUG")


class Callgraph:
    """
    Heuristics-based callgraphs.
    Nodes are function names. Edges (caller, callee, locations) contain the source
    and target nodes, plus a list of locations (file, line) where calls from
    [caller] to [callee] occur.
    """

    # maps each caller to the list of its callees
    succs = {}

    # maps (caller, callee) to the list of call locations
    edges = {}

    def add_edge(self, caller, callee, loc):
        if (caller, callee) in self.edges:
            # edge already exists
            self.edges[(caller, callee)].append(loc)
        else:
            # new edge: check if caller exists
            if not caller in self.succs:
                self.succs[caller] = []
            # add callee as successor of caller
            self.succs[caller].append(callee)
            # add call location to edge information
            self.edges[(caller, callee)] = [loc]

    def nodes(self):
        return self.succs.keys()

    def __repr__(self):
        return f"Callgraph({self.succs}, {self.edges})"


def compute(files):
    cg = Callgraph()
    for f in files:
        file_content = source_filter.open_and_filter(f, not under_test)
        file_lines = file_content.splitlines(keepends=True)
        newlines = function_finder.compute_newline_offsets(file_lines)
        defs = function_finder.find_definitions_and_declarations(
            True, False, f, file_content, file_lines, newlines
        )
        calls = function_finder.find_calls(file_content, newlines)
        for call in calls:
            caller = function_finder.find_caller(defs, call)
            if caller:
                called, line, _ = call
                loc = (f, line)
                if debug:
                    print(f"build_callgraph: {f}:{line}: {caller} -> {called}")
                cg.add_edge(caller, called, loc)
    return cg


def print_edge(cg, caller, called, padding="", end="\n"):
    locs = cg.edges[(caller, called)]
    for (filename, line) in locs:
        print(
            f"{padding}{os.path.relpath(filename)}:{line}: {caller} -> {called}",
            end=end,
        )


def print_cg(cg):
    for (caller, called) in cg.edges:
        print_edge(cg, caller, called)


# note: out _must_ exist (the caller must create it if needed)
def print_cg_dot(cg, out=sys.stdout):
    print("digraph callgraph {", file=out)
    for (caller, called) in cg.edges:
        print(f"  {caller} -> {called};", file=out)
    print("}", file=out)


# succs: dict, input, not modified
# visited: set, input-output, modified
# just_visited: set, input-output, modified
# n: input, not modified
#
# The difference between visited and just_visited is that the latter refers
# to the current bfs; nodes visited in previous bfs already had their cycles
# reported, so we do not report them multiple times.
def cycle_bfs(cg, visited, just_visited, n):
    if debug:
        print(f"cycle_bfs: visited = {visited}, just_visited = {just_visited}, n = {n}")
    just_visited.add(n)
    if n not in cg.succs:
        return []
    fifo = []
    for succ in cg.succs[n]:
        if succ in just_visited:
            return [(n, succ)]
        elif succ in visited:
            # already reported in a previous iteration
            continue
        fifo.append(succ)
    # no cycle found with direct successors, go to next level
    for succ in fifo:
        my_just_visited = just_visited.copy()
        res = cycle_bfs(cg, visited, my_just_visited, succ)
        if res:
            # note that other cycles may not be reported
            caller = res[0][0]
            return [(n, caller)] + res
    return []


def compute_recursive_cycles(cg, acc):
    to_visit = set(cg.nodes())
    if not to_visit:  # empty graph -> no recursion
        return
    visited = set()
    while to_visit:
        just_visited = set()
        n = sorted(list(to_visit))[0]
        cycle = cycle_bfs(cg, visited, just_visited, n)
        visited = visited.union(just_visited)
        if cycle:
            (fst, snd) = cycle[0]
            cycle_start_loc = cg.edges[(fst, snd)][0]
            acc.append((cycle_start_loc, cycle))
        to_visit -= visited


def detect_recursion(cg):
    to_visit = set(cg.nodes())
    if not to_visit:  # empty graph -> no recursion
        return False
    visited = set()
    has_cycle = False
    while to_visit:
        just_visited = set()
        n = sorted(list(to_visit))[0]
        cycle = cycle_bfs(cg, visited, just_visited, n)
        visited = visited.union(just_visited)
        if cycle:
            has_cycle = True
            print("recursive cycle detected: ")
            for (caller, called) in cycle:
                print_edge(cg, caller, called, padding="  ")
        to_visit -= visited
    if not has_cycle:
        print("no recursive calls detected")
