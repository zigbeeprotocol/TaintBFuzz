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

(** Transformations to detect temporal memory errors (e.g., dereference of
    stale pointers). *)

open Cil_types

(* [TODO ARCHI]: change the call convention in this module *)

val enable: bool -> unit
(** Enable/disable temporal transformations *)

val handle_function_parameters: kernel_function -> Env.t -> Env.t
(** [handle_function_parameters kf env] updates the local environment [env],
    according to the parameters of [kf], with statements allowing to track
    referent numbers across function calls. *)

val handle_stmt: stmt -> Env.t -> kernel_function -> Env.t
(** Update local environment ([Env.t]) with statements tracking temporal
    properties of memory blocks *)

val generate_global_init: varinfo -> offset -> init -> stmt option
(** Generate [Some s], where [s] is a statement tracking global initializer
    or [None] if there is no need to track it *)

(*
Local Variables:
compile-command: "make -C ../.."
End:
*)
