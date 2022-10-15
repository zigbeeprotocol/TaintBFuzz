(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file licenses/LGPLv2.1).            *)
(*                                                                        *)
(**************************************************************************)

type node_kind =
  | Scalar of Cil_types.varinfo * Cil_types.typ * Cil_types.offset
  | Composite of Cil_types.varinfo
  | Scattered of Cil_types.lval * Cil_types.kinstr
  | Unknown of Cil_types.lval * Cil_types.kinstr
  | Alarm of Cil_types.stmt * Alarms.alarm
  | AbsoluteMemory
  | String of int * Base.cstring
  | Error of string

type callstack = Callstack.t

type node_locality = {
  loc_file : string;
  loc_callstack : callstack;
}

type node_range =
  | Empty (* No values assigned to the node *)
  | Singleton (* A unique value ever assigned *)
  | Normal of int (* From 0 = almost singleton to 100 = almost all possible values *)
  | Wide (* Too many values for the type to be reasonable *)

type 'a computation = NotDone | Partial of 'a | Done

type node = {
  node_key : int;
  node_kind : node_kind;
  node_locality : node_locality;
  mutable node_is_root : bool;
  mutable node_hidden : bool;
  mutable node_values : Cvalue.V.t option;
  mutable node_range : node_range;
  mutable node_writes_computation : (Cil_types.stmt list) computation;
  mutable node_reads_computation : (Cil_types.stmt list) computation;
  mutable node_writes_stmts : Cil_types.stmt list;
}

type dependency_kind = Callee | Data | Address | Control | Composition

type dependency = {
  dependency_key : int;
  dependency_kind : dependency_kind;
  mutable dependency_origins : Cil_types.stmt list;
}

type graph_diff = {
  last_root: node option;
  added_nodes: node list;
  removed_nodes: node list;
}

type 'a range = {
  backward: 'a;
  forward: 'a;
}

type window = {
  perception: int option range; (* depth of exploration *)
  horizon: int option range; (* hide beyond horizon ; None for infinite *)
}
