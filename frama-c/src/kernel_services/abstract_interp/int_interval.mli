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

(** Integer intervals with congruence.
    An interval defined by [min, max, rem, modu] represents all integers
    between the bounds [min] and [max] and congruent to [rem] modulo [modu].
    A value of [None] for [min] (resp. [max]) represents -infinity
    (resp. +infinity). [modu] is > 0, and [0 <= rem < modu]. *)

open Lattice_bounds

include Datatype.S_with_collections

include Eva_lattice_type.Full_AI_Lattice_with_cardinality
  with type t := t
   and type widen_hint = Integer.t * Datatype.Integer.Set.t

(** Checks that the interval defined by [min, max, rem, modu] is well formed. *)
val check:
  min:Integer.t option -> max:Integer.t option ->
  rem:Integer.t -> modu:Integer.t -> unit

(** Makes the interval of all integers between [min] and [max] and congruent
    to [rem] modulo [modu]. Fails if these conditions does not hold:
    - min ≤ max
    - 0 ≤ rem < modu
    - min ≅ rem [modu] ∧ max ≅ rem [modu] *)
val make:
  min:Integer.t option -> max:Integer.t option ->
  rem:Integer.t -> modu:Integer.t -> t

(** Makes the interval of all integers between [min] and [max]. *)
val inject_range: Integer.t option -> Integer.t option -> t

(** Returns the bounds of the given interval. [None] means infinity. *)
val min_and_max: t -> Integer.t option * Integer.t option

(** Returns the bounds and the modulo of the given interval. *)
val min_max_rem_modu:
  t -> Integer.t option * Integer.t option * Integer.t * Integer.t

(** [mem i t] returns true iff the integer [i] is in the interval [t]. *)
val mem: Integer.t -> t -> bool

(** Returns the number of integers represented by the given interval.
    Returns [None] if the interval represents an infinite number of integers. *)
val cardinal: t -> Integer.t option

val complement_under: min:Integer.t -> max:Integer.t -> t -> t or_bottom
(** Returns an under-approximation of the integers between [min] and [max]
    that are *not* represented by the given interval. *)

(** {2 Interval semantics.} *)

(** See {!Int_val} for more details. *)

val add_singleton_int: Integer.t -> t -> t
val add: t -> t -> t
val add_under: t -> t -> t or_bottom
val neg: t -> t
val abs: t -> t

val scale: Integer.t -> t -> t
val scale_div: pos:bool -> Integer.t -> t -> t
val scale_div_under: pos:bool -> Integer.t -> t -> t or_bottom
val scale_rem: pos:bool -> Integer.t -> t -> t

val mul: t -> t -> t
val div: t -> t -> t or_bottom
val c_rem: t -> t -> t or_bottom

val cast: size:Integer.t -> signed:bool -> t -> t

(** {2 Misc.} *)

val subdivide: t -> t * t

val reduce_sign: t -> bool -> t or_bottom
val reduce_bit: int -> t -> bool -> t or_bottom

val fold_int: ?increasing:bool -> (Integer.t -> 'a -> 'a) -> t -> 'a -> 'a
