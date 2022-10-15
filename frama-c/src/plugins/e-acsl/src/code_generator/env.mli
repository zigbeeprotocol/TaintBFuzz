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

open Cil_types
open Analyses_types
open Contract_types

(** Environments.

    Environments handle all the new C constructs (variables, statements and
    annotations. *)

type t

val empty: t

val has_no_new_stmt: t -> bool
(** Assume that a local context has been previously pushed.
    @return true iff the given env does not contain any new statement. *)

type localized_scope =
  | LGlobal
  | LFunction of kernel_function
  | LLocal_block of kernel_function

val new_var:
  loc:location -> ?scope:Varname.scope -> ?name:string ->
  t -> kernel_function -> term option -> typ ->
  (varinfo -> exp (* the var as exp *) -> stmt list) ->
  varinfo * exp * t
(** [new_var env t ty mk_stmts] extends [env] with a fresh variable of type
    [ty] corresponding to [t]. [scope] is the scope of the new variable (default
    is [Block]).
    @return this variable as both a C variable and a C expression already
    initialized by applying it to [mk_stmts]. *)

val new_var_and_mpz_init:
  loc:location -> ?scope:Varname.scope -> ?name:string ->
  t -> kernel_function -> term option ->
  (varinfo -> exp (* the var as exp *) -> stmt list) ->
  varinfo * exp * t
(** Same as [new_var], but dedicated to mpz_t variables initialized by
    {!Mpz.init}. *)

val rtl_call_to_new_var:
  loc:location -> ?scope:Varname.scope -> ?name:string ->
  t -> kernel_function -> term option -> typ ->
  string -> exp list ->
  exp * t
(** [rtl_call_to_new_var env t ty name args] Same as [new_var] but initialize
    the variable with a call to the RTL function [name] with the given [args].
*)

module Logic_binding: sig
  val add: ?ty:typ -> t -> kernel_function -> logic_var -> varinfo * exp * t
  (* Add a new C binding to the list of bindings for the logic variable. *)

  val add_binding: t -> logic_var -> varinfo -> t
  (* [add_binding env lv vi] defines [vi] as the latest C binding for
     [lv]. *)

  val get: t -> logic_var -> varinfo
  (* Return the latest C binding. *)

  val remove: t -> logic_var -> unit
  (* Remove the latest C binding. *)

end

val add_assert: kernel_function -> stmt -> predicate -> unit
(** [add_assert env s p] associates the assertion [p] to the statement [s] in
    the environment [env]. *)

val add_stmt: ?post:bool -> t -> stmt -> t
(** [add_stmt env s] extends [env] with the new statement [s].
    [post] indicates that [stmt] should be added after the target statement. *)

val extend_stmt_in_place: t -> stmt -> label:logic_label -> block -> t
(** [extend_stmt_in_place env stmt ~label b] modifies [stmt] in place in
    order to add the given [block]. If [label] is [Here] or [Post],
    then this block is guaranteed to be at the first place of the resulting
    [stmt] whatever modification will be done by the visitor later. *)

val push: t -> t
(** Push a new local context in the environment *)

type where = Before | Middle | After
val pop_and_get:
  ?split:bool -> t -> stmt -> global_clear:bool -> where -> block * t
(** Pop the last local context and get back the corresponding new block
    containing the given [stmt] at the given place ([Before] is before the code
    corresponding to annotations, [After] is after this code and [Middle] is
    between the stmt corresponding to annotations and the ones for freeing the
    memory. When [where] is [After], set [split] to true in order to generate
    one block which contains exactly 2 stmt: one for [stmt] and one sub-block
    for the generated stmts. *)

val pop: t -> t
(** Pop the last local context (ignore the corresponding new block if any *)

val transfer: from:t -> t -> t
(** Pop the last local context of [from] and push it into the other env. *)

val get_generated_variables: t -> (varinfo * localized_scope) list
(** All the new variables local to the visited function. *)

module Logic_scope: sig
  val get: t -> Lscope.t
  (** Return the logic scope associated to the environment. *)

  val extend: t -> lscope_var -> t
  (** Add a new logic variable with its associated information in the
      logic scope of the environment. *)

  val remove: t -> lscope_var -> t
  (** Remove a logic variable and its associated information from the logic
      scope of the environment. *)

  val reset: t -> t
  (** Return a new environment in which the logic scope is reset
      iff [set_reset _ true] has been called beforehand. Do nothing otherwise. *)

  val set_reset: t -> bool -> t
  (** Setter of the information indicating whether the logic scope should be
      reset at next call to [reset]. *)

  val get_reset: t -> bool
  (** Getter of the information indicating whether the logic scope should be
      reset at next call to [reset]. *)
end

(* ************************************************************************** *)
(** {2 Current annotation kind} *)
(* ************************************************************************** *)

val annotation_kind: t -> annotation_kind
val set_annotation_kind: t -> annotation_kind -> t

(* ************************************************************************** *)
(** {2 Loop annotations} *)
(* ************************************************************************** *)

val push_loop: t -> t
val set_loop_variant: ?measure:logic_info -> t -> term -> t
val add_loop_invariant: t -> toplevel_predicate -> t
val top_loop_variant: t -> (term * logic_info option) option
val top_loop_invariants: t -> toplevel_predicate list
val pop_loop: t -> t

(* ************************************************************************** *)
(** {2 RTEs} *)
(* ************************************************************************** *)

val set_rte: t -> bool -> t
(** [set_rte env x] sets RTE generation to x for the given environment *)

val generate_rte: t -> bool
(** Returns the current value of RTE generation for the given environment *)

module Local_vars: sig
  val push_new: t -> t
  val add: t -> Typing.number_ty -> t
  val get: t -> Typing.Function_params_ty.t
end

(* ************************************************************************** *)
(** {2 Context for error handling} *)
(* ************************************************************************** *)

module Context: sig
  val save: t -> unit
end

val handle_error: (t -> t) -> t -> t
(** Run the closure with the given environment and handle potential errors.
    Restore the globals of the environment to the last time [Env.Context.save]
    was called and return it in case of errors. *)

val handle_error_with_args: (t * 'a -> t * 'a) -> t * 'a -> t * 'a
(** Run the closure with the given environment and arguments  and handle
    potential errors.
    Restore the globals of the environment to the last time [Env.Context.save]
    was called and return it in case of errors. *)

val not_yet: t -> string -> 'a
(** Save the current context and raise [Error.Not_yet] exception. *)

(* ************************************************************************** *)
(** {2 Current environment kinstr} *)
(* ************************************************************************** *)

val set_kinstr: t -> kinstr -> t
val get_kinstr: t -> kinstr

(* ************************************************************************** *)
(** {2 Contracts} *)
(* ************************************************************************** *)

val push_contract: t -> contract -> t
(** Push a contract to the environment's stack *)

val pop_and_get_contract: t -> contract * t
(** Pop and return the top contract of the environment's stack *)

(* ************************************************************************** *)
(** {2 Utilities} *)
(* ************************************************************************** *)

val with_params: ?rte:bool -> ?kinstr:kinstr -> f:(t -> t) -> t -> t
(** [with_params ~rte ~kinstr ~f env] executes the given closure with the given
    environment after having set RTE generation to [rte] and current kinstr to
    [kinstr].
    [f] is a closure that takes an environment and returns an environment.
    The environment returned by the closure is updated to restore the RTE
    generation and kinstr attributes to the values of the original environment,
    then is returned. *)

val with_params_and_result:
  ?rte:bool -> ?kinstr:kinstr -> f:(t -> 'a * t) -> t -> 'a * t
(** [with_params_and_result ~rte ~kinstr ~f env] executes the given closure with
    the given environment after having set RTE generation to [rte] and current
    kinstr to [kinstr].
    [f] is a closure that takes an environment and returns a pair where the
    first member is an arbitrary value and the second member is the environment.
    The environment returned by the closure is updated to restore the RTE
    generation and kinstr attributes to the values of the original environment,
    then the function returns the arbitrary value returned by the closure along
    with the updated environment. *)

val pretty: Format.formatter -> t -> unit

(*
Local Variables:
compile-command: "make -C ../.."
End:
*)
