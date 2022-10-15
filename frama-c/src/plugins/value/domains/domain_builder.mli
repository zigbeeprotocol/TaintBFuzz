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

(** Automatic builders to complete abstract domains from different
    simplified interfaces. *)

open Cil_types
open Eval

module type InputDomain = sig
  include Datatype.S
  val top: t
  val join: t -> t -> t
end

(** Part of an abstract domain signature automatically built by the
    {!Complete} functor. These functions can be redefined to achieve
    better precision or performance. See {!Abstract_domain} for more details. *)
module type LeafDomain = sig
  type t

  val backward_location: t -> lval -> typ -> 'loc -> 'v -> ('loc * 'v) or_bottom
  val reduce_further: t -> exp -> 'v -> (exp * 'v) list

  val evaluate_predicate:
    t Abstract_domain.logic_environment -> t -> predicate -> Alarmset.status
  val reduce_by_predicate:
    t Abstract_domain.logic_environment -> t -> predicate -> bool -> t or_bottom
  val interpret_acsl_extension:
    acsl_extension -> t Abstract_domain.logic_environment -> t -> t

  val enter_loop: stmt -> t -> t
  val incr_loop_counter: stmt -> t -> t
  val leave_loop: stmt -> t -> t

  val filter: kernel_function -> [`Pre | `Post] -> Base.Hptset.t -> t -> t
  val reuse:
    kernel_function -> Base.Hptset.t ->
    current_input:t -> previous_output:t -> t

  val show_expr: 'a -> t -> Format.formatter -> exp -> unit
  val post_analysis: t Lattice_bounds.or_bottom -> unit

  module Store: Domain_store.S with type t := t

  val key: t Abstract_domain.key
end

(** Automatically builds some functions of an abstract domain. *)
module Complete (Domain: InputDomain) : LeafDomain with type t := Domain.t

module Complete_Minimal
    (Value: Abstract_value.S)
    (Location: Abstract_location.S)
    (Domain: Simpler_domains.Minimal)
  : Abstract_domain.Leaf with type value = Value.t
                          and type location = Location.location
                          and type state = Domain.t

module Complete_Minimal_with_datatype
    (Value: Abstract_value.S)
    (Location: Abstract_location.S)
    (Domain: Simpler_domains.Minimal_with_datatype)
  : Abstract_domain.Leaf with type value = Value.t
                          and type location = Location.location
                          and type state = Domain.t

module Complete_Simple_Cvalue
    (Domain: Simpler_domains.Simple_Cvalue)
  : Abstract_domain.Leaf with type value = Cvalue.V.t
                          and type location = Precise_locs.precise_location
                          and type state = Domain.t

(* Restricts an abstract domain on specific functions. The domain will only be
   enabled on the given functions. Moreover, a mode is associated to each of
   these functions, allowing (or not) the domain to infer or use properties
   in the current function and in all functions called from it.
   See {!Domain_mode} for more details. *)
module Restrict
    (Value: Abstract_value.S)
    (Domain: Abstract.Domain.Internal with type value = Value.t)
    (Scope: sig val functions: Domain_mode.function_mode list end)
  : Abstract.Domain.Internal with type value = Value.t
                              and type location = Domain.location
