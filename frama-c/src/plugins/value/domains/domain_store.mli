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
open Eval

module type InputDomain = sig
  include Datatype.S
  val top: t
  val join: t -> t -> t
end

(** Automatic storage of the states computed during the analysis. *)
module type S = sig
  type t

  (** Called once at the analysis beginning for the entry state of the main
      function. The boolean indicates whether the states of this domain must be
      saved during the analysis, according to options -eva-no-results. If it is
      false, register functions do nothing, and get functions return Top. *)
  val register_global_state: bool -> t or_bottom -> unit

  val register_initial_state: Value_types.callstack -> t -> unit
  val register_state_before_stmt: Value_types.callstack -> stmt -> t -> unit
  val register_state_after_stmt: Value_types.callstack -> stmt -> t -> unit

  (** Allows accessing the states inferred by an Eva analysis after it has
      been computed with the domain enabled. *)
  val get_global_state: unit -> t or_bottom
  val get_initial_state: kernel_function -> t or_bottom
  val get_initial_state_by_callstack:
    ?selection:callstack list ->
    kernel_function -> t Value_types.Callstack.Hashtbl.t or_top_bottom

  val get_stmt_state: after:bool -> stmt -> t or_bottom
  val get_stmt_state_by_callstack:
    ?selection:callstack list ->
    after:bool -> stmt -> t Value_types.Callstack.Hashtbl.t or_top_bottom

  val mark_as_computed: unit -> unit
  val is_computed: unit -> bool
end

module Make (Domain : InputDomain) : S with type t := Domain.t
