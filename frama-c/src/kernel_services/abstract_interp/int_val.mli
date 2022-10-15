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

(** Integer values abstractions: an abstraction represents a set of integers.
    Provided with a lattice structure and over-approximations of arithmetic
    operations. *)

(** Abstractions do not represent the empty set. Instead, operations creating
    empty sets return `Bottom. *)
open Lattice_bounds

include Datatype.S_with_collections

module Widen_Hints = Datatype.Integer.Set
type size_widen_hint = Integer.t
type generic_widen_hint = Widen_Hints.t

include Eva_lattice_type.Full_AI_Lattice_with_cardinality
  with type t := t
   and type widen_hint = size_widen_hint * generic_widen_hint

val zero: t
val one: t
val minus_one: t
val zero_or_one: t

val positive_integers: t
(** All positive integers, including 0. *)

val negative_integers: t
(** All negative integers, including 0. *)

(** {2 Building.} *)

(** Returns an exact abstraction of the given integer. *)
val inject_singleton: Integer.t -> t

(** [inject_range min max] returns an abstraction of all integers between
    [min] and [max] included. [None] means that the abstraction is unbounded. *)
val inject_range: Integer.t option -> Integer.t option -> t

(** Builds an abstraction of all integers between [min] and [max] included and
    congruent to [rem] modulo [modu]. For [min] and [max], [None] is the
    corresponding infinity. Checks that [min] <= [max], [modu] > 0 and
    0 <= [rest] < [modu], and fails otherwise. If possible, reduces [min] and
    [max] according to the modulo. *)
val inject_interval:
  min: Integer.t option -> max: Integer.t option ->
  rem: Integer.t -> modu: Integer.t ->
  t

(** As [inject_interval], but also checks that [min] and [max] are congruent to
    [rem] modulo [modu]. *)
val make:
  min: Integer.t option -> max: Integer.t option ->
  rem: Integer.t -> modu: Integer.t ->
  t

(** {2 Accessors.} *)

(** Returns the smallest integer represented by an abstraction.
    Returns None if it does not exist, i.e. if the abstraction is unbounded. *)
val min_int: t -> Integer.t option

(** Returns the highest integer represented by an abstraction.
    Returns None if it does not exist, i.e. if the abstraction is unbouded. *)
val max_int: t -> Integer.t option

(** Returns the smallest and highest integers represented by an abstraction. *)
val min_and_max: t -> Integer.t option * Integer.t option

(** Returns [min, max, rem, modu] such that for all integers [i] represented by
    the given abstraction, [i] satisfies min ≤ i ≤ max and i ≅ rem [modu]. *)
val min_max_rem_modu:
  t -> Integer.t option * Integer.t option * Integer.t * Integer.t

exception Not_Singleton

(** Projects a singleton abstraction into an integer.
    @raise Not_Singleton if the cardinal of the argument is not 1. *)
val project_int: t -> Integer.t

(** Is an abstraction internally represented as a small integer set? *)
val is_small_set: t -> bool
val project_small_set: t -> Integer.t list option

(** {2 Cardinality.} *)

val is_singleton: t -> bool
val cardinal_zero_or_one: t -> bool
val cardinal: t -> Integer.t option
val cardinal_estimate: size:Integer.t -> t -> Integer.t
val cardinal_less_than: t -> int -> int
val cardinal_is_less_than: t -> int -> bool

val is_zero: t -> bool
val contains_zero: t -> bool
val contains_non_zero: t -> bool

(** {2 Arithmetics.} *)

val add: t -> t -> t
(** Addition of two integer abstractions. *)

val add_under: t -> t -> t or_bottom
(** Under-approximation of the addition of two integer abstractions *)

val add_singleton: Integer.t -> t -> t
(** Addition of an integer abstraction with a singleton integer.
    Exact operation. *)

val neg: t -> t
(** Negation of an integer abstraction. *)

val abs: t -> t
(** Absolute value of an integer abstraction. *)

val scale: Integer.t -> t -> t
(** [scale f v] returns an abstraction of the integers [f * x]
    for all [x] in [v]. This operation is exact. *)

val scale_div: pos:bool -> Integer.t -> t -> t
(** [scale_div f v] is an over-approximation of the elements [x / f] for all
    elements [x] in [v]. Uses the computer division (like in C99) if [pos] is
    false, and the euclidean division if [pos] is true. *)

val scale_div_under: pos:bool -> Integer.t -> t -> t or_bottom
(** Under-approximation of the division. *)

val scale_rem: pos:bool -> Integer.t -> t -> t
(** Over-approximation of the remainder of the division. Uses the computer
    division (like in C99) if [pos] is false, and the euclidean division if
    [pos] is true. *)

val mul: t -> t -> t
val div: t -> t -> t or_bottom
val c_rem: t -> t -> t or_bottom
val shift_left:  t -> t -> t or_bottom
val shift_right: t -> t -> t or_bottom

val bitwise_and: t -> t -> t
val bitwise_or: t -> t -> t
val bitwise_xor: t -> t -> t
val bitwise_signed_not: t -> t
val bitwise_unsigned_not: size:int -> t -> t

(** {2 Misc} *)

val cast_int_to_int: size:Integer.t -> signed:bool -> t -> t

(** Splits an abstraction into two abstractions. *)
val subdivide: t -> t * t

(** Extracts bits from [start] to [stop] from the given integer abstraction,
    [start] and [stop] being included. *)
val extract_bits: start:Integer.t -> stop:Integer.t -> t -> t

(** Builds an abstraction of all integers in a C integer type. *)
val create_all_values: signed:bool -> size:int -> t

(** [all_values ~size v] returns true iff v contains all integer values
    representable in [size] bits. *)
val all_values: size:Integer.t -> t -> bool

val complement_under: size:int -> signed:bool -> t -> t or_bottom
(** Returns an under-approximation of the integers of the given size and
    signedness that are *not* represented by the given value. *)

(** Iterates on all integers represented by an abstraction, in increasing order
    by default. If [increasing] is set to false, iterate by decreasing order.
    @raise Abstract_interp.Error_Top if the abstraction is unbounded. *)
val fold_int: ?increasing:bool -> (Integer.t -> 'a -> 'a) -> t -> 'a -> 'a
