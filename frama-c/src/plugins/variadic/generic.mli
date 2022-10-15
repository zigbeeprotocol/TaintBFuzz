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

(* The vpar formal parameter *)
val vpar : string * Cil_types.typ * Cil_types.attributes

(* Shallow translation of variadic types *)
val translate_type : Cil_types.typ -> Cil_types.typ

(* Adds the vpar parameter to variadic functions *)
val add_vpar : Cil_types.varinfo -> unit

(* Translation of va_* builtins *)
val translate_va_builtin : Cil_types.fundec -> Cil_types.instr ->
  Cil_types.instr list

(* Generic translation of calls *)
val translate_call : fundec:Cil_types.fundec -> ghost:bool ->
  Cil_types.block -> Cil_types.location ->
  (Cil_types.exp -> Cil_types.exp list -> Cil_types.instr) ->
  Cil_types.exp -> Cil_types.exp list ->
  Cil_types.instr list
