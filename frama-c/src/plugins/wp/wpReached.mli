(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(** Reachability for Smoke Tests *)
(* -------------------------------------------------------------------------- *)

open Cil_types

type reachability
(** control flow graph dedicated to smoke tests *)

val is_predicate : bool -> predicate -> bool
(** If returns [true] the predicate has always the given boolean value. *)

val is_dead_annot : code_annotation -> bool
(** False assertions and loop invariant.
    Hence, also includes completely unrolled loop. *)

val is_dead_code : stmt -> bool
(** Checks whether the stmt has a dead-code annotation. *)

val reachability : Kernel_function.t -> reachability
(** memoized reached cfg for function *)

val smoking : reachability -> Cil_types.stmt -> bool
(** Returns whether a stmt need a smoke tests to avoid being unreachable.
    This is restricted to assignments, returns and calls not dominated
    another smoking statement. *)

val dump : dir:Datatype.Filepath.t -> Kernel_function.t -> reachability -> unit

val set_doomed : Emitter.t -> WpPropId.prop_id -> unit

val unreachable_proved : int ref
val unreachable_failed : int ref

val set_unreachable : WpPropId.prop_id -> unit

(* -------------------------------------------------------------------------- *)
