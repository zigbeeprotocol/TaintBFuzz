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

module type Results = sig
  type state
  type value
  type location

  val get_global_state: unit -> state or_top_bottom
  val get_stmt_state : after:bool -> stmt -> state or_top_bottom
  val get_stmt_state_by_callstack:
    ?selection:callstack list ->
    after:bool -> stmt -> state Value_types.Callstack.Hashtbl.t or_top_bottom
  val get_initial_state:
    kernel_function -> state or_top_bottom
  val get_initial_state_by_callstack:
    ?selection:callstack list ->
    kernel_function -> state Value_types.Callstack.Hashtbl.t or_top_bottom

  val eval_expr : state -> exp -> value evaluated
  val copy_lvalue: state -> lval -> value flagged_value evaluated
  val eval_lval_to_loc: state -> lval -> location evaluated
  val eval_function_exp:
    state -> ?args:exp list -> exp -> kernel_function list evaluated
  val assume_cond : stmt -> state -> exp -> bool -> state or_bottom
end


module Make (Abstract: Abstractions.S) : sig

  val compute_from_entry_point : kernel_function -> lib_entry:bool -> unit
  val compute_from_init_state: kernel_function -> Abstract.Dom.t -> unit

  include Results with type state := Abstract.Dom.state
                   and type value := Abstract.Val.t
                   and type location := Abstract.Loc.location
end


module type S = sig
  include Abstractions.Eva
  include Results with type state := Dom.state
                   and type value := Val.t
                   and type location := Loc.location
end

val current_analyzer : unit -> (module S)
(** The abstractions used in the latest analysis, and its results. *)

val register_hook: ((module S) -> unit) -> unit
(** Registers a hook that will be called each time the [current] analyzer
    is changed. This happens when a new analysis is run with different
    abstractions than before, or when the current project is changed. *)

val force_compute : unit -> unit
(** Perform a full analysis, starting from the [main] function. *)

[@@@ api_start]
val compute : unit -> unit
(** Computes the Eva analysis, if not already computed, using the entry point
    of the current project. You may set it with {!Globals.set_entry_point}.
    @raise Globals.No_such_entry_point if the entry point is incorrect
    @raise Db.Value.Incorrect_number_of_arguments if some arguments are
    specified for the entry point using {!Db.Value.fun_set_args}, and
    an incorrect number of them is given.
    @plugin development guide *)

val is_computed : unit -> bool
(** Return [true] iff the Eva analysis has been done. *)

val self : State.t
(** Internal state of Eva analysis from projects viewpoint. *)

type computation_state = NotComputed | Computing | Computed | Aborted
(** Computation state of the analysis. *)

val current_computation_state : unit -> computation_state
(** Get the current computation state of the analysis, updated by
    [force_compute] and states updates. *)

val register_computation_hook: ?on:computation_state ->
  (computation_state -> unit) -> unit
(** Registers a hook that will be called each time the analysis starts or
    finishes. If [on] is given, the hook will only be called when the
    analysis switches to this specific state. *)

(** Kind of results for the analysis of a function body. *)
type results =
  | Complete
  (** The results are complete: they cover all possible call contexts of the
      given function. *)
  | Partial
  (** The results are partial, as the functions has not been analyzed in all
      possible call contexts. This happens for recursive functions that are
      not completely unrolled, or if the analysis has stopped unexpectedly. *)
  | NoResults
  (** No results were saved for the function, due to option -eva-no-results.
      Any request at a statement of this function will lead to a Top result. *)

(* Analysis status of a function. *)
type status =
  | Unreachable
  (** The function has not been reached by the analysis. Any request in this
      function will lead to a Bottom result. *)
  | SpecUsed
  (** The function specification has been used to interpret its calls:
      its body has not been analyzed. Any request at a statement of this
      function will lead to a Bottom result. *)
  | Builtin of string
  (** The builtin of the given name has been used to interpret the function:
      its body has not been analyzed. Any request at a statement of this
      function will lead to a Bottom result. *)
  | Analyzed of results
  (** The function body has been analyzed. *)

(** Returns the analysis status of a given function. *)
val status: Cil_types.kernel_function -> status

(** Does the analysis ignores the body of a given function, and uses instead
    its specification or a builtin to interpret it?
    Please use {!Eva.Results.are_available} instead to known whether results
    are available for a given function. *)
val use_spec_instead_of_definition: Cil_types.kernel_function -> bool

(** Returns [true] if the user has requested that no results should be recorded
    for the given function. Please use {!Eva.Results.are_available} instead
    to known whether results are available for a given function. *)
val save_results: Cil_types.kernel_function -> bool
[@@@ api_end]

val cvalue_initial_state: unit -> Cvalue.Model.t
(** Return the initial state of the cvalue domain only. *)
