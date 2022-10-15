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

(** Sets over ordered types.

    This module implements the set data structure.
    All operations over sets are purely applicative (no side-effects). *)

(** Subset of the OCaml Set.S signature. *)
module type S_Basic_Compare =
sig
  type elt
  type t
  val empty: t
  val is_empty: t -> bool
  val mem: elt -> t -> bool
  val add: elt -> t -> t
  val singleton: elt -> t
  val remove: elt -> t -> t
  val union: t -> t -> t
  val inter: t -> t -> t
  val diff: t -> t -> t
  val compare: t -> t -> int
  val equal: t -> t -> bool
  val subset: t -> t -> bool
  val iter: (elt -> unit) -> t -> unit
  val fold: (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val for_all: (elt -> bool) -> t -> bool
  val exists: (elt -> bool) -> t -> bool
  val filter: (elt -> bool) -> t -> t
  val partition: (elt -> bool) -> t -> t * t
  val cardinal: t -> int
  val elements: t -> elt list
  val choose: t -> elt
  val find: elt -> t -> elt
  val of_list: elt list -> t
end

(** Output signature of the functor {!Set.Make}. *)
module type S = sig
  type 'a map

  include Datatype.S_with_collections with type t = unit map
  include S_Basic_Compare with type t := t
  (** The datatype of sets. *)

  val contains_single_elt: t -> elt option

  val intersects: t -> t -> bool
  (** [intersects s1 s2] returns [true] if and only if [s1] and [s2]
      have an element in common *)

  type action = Neutral | Absorbing | Traversing of (elt -> bool)

  val merge :
    cache:Hptmap_sig.cache_type ->
    symmetric:bool ->
    idempotent:bool ->
    decide_both:(elt -> bool) ->
    decide_left:action ->
    decide_right:action ->
    t -> t -> t

  val from_map: 'a map -> t

  val fold2_join_heterogeneous:
    cache:Hptmap_sig.cache_type ->
    empty_left:('a map -> 'b) ->
    empty_right:(t -> 'b) ->
    both:(elt -> 'a -> 'b) ->
    join:('b -> 'b -> 'b) ->
    empty:'b ->
    t -> 'a map ->
    'b

  val replace: elt map -> t -> bool * t
  (** [replace shape set] replaces the elements of [set] according to [shape].
      The returned boolean indicates whether the set has been modified; it is
      false when the intersection between [shape] and [set] is empty. *)

  (** Clear all the caches used internally by the functions of this module.
      Those caches are not project-aware, so this function must be called
      at least each a project switch occurs. *)
  val clear_caches: unit -> unit

  val pretty_debug: t Pretty_utils.formatter
end

module Make(X: Hptmap.Id_Datatype)
    (Initial_Values : sig val v : X.t list list end)
    (Datatype_deps: sig val l : State.t list end) :
sig
  include S with type elt = X.t
             and type 'a map = 'a Hptmap.Shape(X).map
  val self : State.t
end

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
