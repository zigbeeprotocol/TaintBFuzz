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

[@@@ api_start]

(** Eva analysis builtins for the cvalue domain, more efficient than their
    equivalent in C. *)

open Cil_types

exception Invalid_nb_of_args of int
exception Outside_builtin_possibilities

(* Signature of a builtin: type of the result, and type of the arguments. *)
type builtin_type = unit -> typ * typ list

(** Can the results of a builtin be cached? See {!Eval} for more details.*)
type cacheable = Eval.cacheable = Cacheable | NoCache | NoCacheCallers

type full_result = {
  c_values: (Cvalue.V.t option * Cvalue.Model.t) list;
  (** A list of results, consisting of:
      - the value returned (ie. what is after the 'return' C keyword)
      - the memory state after the function has been executed. *)
  c_clobbered: Base.SetLattice.t;
  (** An over-approximation of the bases in which addresses of local variables
      might have been written *)
  c_from: (Function_Froms.froms * Locations.Zone.t) option;
  (** If not None, the froms of the function, and its sure outputs;
      i.e. the dependencies of the result and of each zone written to. *)
}

(** The result of a builtin can be given in different forms. *)
type call_result =
  | States of Cvalue.Model.t list
  (** A disjunctive list of post-states at the end of the C function.
      Can only be used if the C function does not write the address of local
      variables, does not read other locations than the call arguments, and
      does not write other locations than the result. *)
  | Result of Cvalue.V.t list
  (** A disjunctive list of resulting values. The specification is used to
      compute the post-state, in which the result is replaced by the values
      computed by the builtin. *)
  | Full of full_result
  (** See [full_result] type. *)

(** Type of a cvalue builtin, whose arguments are:
    - the memory state at the beginning of the function call;
    - the list of arguments of the function call. *)
type builtin = Cvalue.Model.t -> (exp * Cvalue.V.t) list -> call_result

(** [register_builtin name ?replace ?typ cacheable f] registers the function [f]
    as a builtin to be used instead of the C function of name [name].
    If [replace] is provided, the builtin is also used instead of the C function
    of name [replace], unless option -eva-builtin-auto is disabled.
    If [typ] is provided, consistency between the expected [typ] and the type of
    the C function is checked before using the builtin.
    The results of the builtin are cached according to [cacheable]. *)
val register_builtin:
  string -> ?replace:string -> ?typ:builtin_type -> cacheable -> builtin -> unit

(** Has a builtin been registered with the given name? *)
val is_builtin: string -> bool
[@@@ api_end]

(** Prepares the builtins to be used for an analysis. Must be called at the
    beginning of each Eva analysis. Warns about builtins of incompatible types,
    builtins without an available specification and builtins overriding function
    definitions. *)
val prepare_builtins: unit -> unit

(** Is a given function replaced by a builtin? *)
val is_builtin_overridden: kernel_function -> bool

(** [clobbered_set_from_ret state ret] can be used for functions that return
    a pointer to where they have written some data. It returns all the bases
    of [ret] whose contents may contain local variables. *)
val clobbered_set_from_ret: Cvalue.Model.t -> Cvalue.V.t -> Base.SetLattice.t

type call = (Precise_locs.precise_location, Cvalue.V.t) Eval.call
type result = Cvalue_domain.State.t

(** Returns the cvalue builtin for a function, if any. Also returns the name of
    the builtin and the specification of the function; the preconditions must be
    evaluated along with the builtin.
    [prepare_builtins] should have been called before using this function. *)
val find_builtin_override:
  kernel_function -> (string * builtin * cacheable * funspec) option

(* Applies a cvalue builtin for the given call, in the given cvalue state. *)
val apply_builtin:
  builtin -> call -> pre:Cvalue.Model.t -> post:Cvalue.Model.t -> result list


(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
