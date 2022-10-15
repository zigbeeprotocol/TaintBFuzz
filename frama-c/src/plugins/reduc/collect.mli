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

open Cil_types

type 'a alarm_component = Emitter.t ->
  kernel_function ->
  stmt ->
  rank:int -> Alarms.alarm -> code_annotation -> 'a -> 'a

type env

type annoth = AnnotAll | AnnotInout

val empty_env: annoth -> env

val get_relevant: env alarm_component (* Set(loc) * Set(exp) ? *)

val should_annotate_stmt: env -> stmt -> bool
val get_relevant_vars_stmt: env -> kernel_function -> stmt -> lval list
