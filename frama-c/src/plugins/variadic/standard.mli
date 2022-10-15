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

(* Ugly ref *)
val new_globals : (Cil_types.global list) ref

type call_builder  = Cil_types.exp -> Cil_types.exp list -> Cil_types.instr

exception Translate_call_exn of Cil_types.varinfo

val fallback_fun_call : callee:Cil_types.varinfo -> Cil_types.location ->
  call_builder -> Va_types.variadic_function -> Cil_types.exp list ->
  Cil_types.instr list

val aggregator_call : fundec:Cil_types.fundec -> ghost:bool ->
  Va_types.aggregator -> Cil_types.block -> Cil_types.location ->
  call_builder -> Va_types.variadic_function -> Cil_types.exp list ->
  Cil_types.instr list

val overloaded_call : fundec:Cil_types.fundec -> Va_types.overload ->
  Cil_types.block -> Cil_types.location -> call_builder ->
  Va_types.variadic_function -> Cil_types.exp list ->
  Cil_types.instr list

val format_fun_call : fundec:Cil_types.fundec -> Environment.t ->
  Va_types.format_fun -> Cil_types.block -> Cil_types.location ->
  call_builder -> Va_types.variadic_function -> Cil_types.exp list ->
  Cil_types.instr list
