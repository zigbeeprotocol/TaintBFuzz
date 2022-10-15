(**************************************************************************)
(*                                                                        *)
(*  This file is part of the Frama-C's E-ACSL plug-in.                    *)
(*                                                                        *)
(*  Copyright (C) 2012-2021                                               *)
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

(** Code generation for libc functions *)

open Cil_types

val is_writing_memory: varinfo -> bool
(** @return true if the function is a libc function that writes memory. *)

val update_memory_model:
  loc:location ->
  ?result:lval ->
  Env.t ->
  kernel_function ->
  varinfo ->
  exp list ->
  lval option * Env.t
(** [update_memory_model ~loc env kf ?result caller args] generates code in
    [env] to update the memory model after executing the libc function [caller]
    with the given [args].
    @return a tuple [result_opt, env] where [result_opt] is an option with
    the lvalue for the result of the function and [env] is the updated
    environement. *)
