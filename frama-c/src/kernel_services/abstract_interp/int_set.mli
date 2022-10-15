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

(** Small sets of integers.

    Above a certain limit fixed by [set_small_cardinal], these sets must be
    converted into intervals. The functions that make the set grow returns a
    [set_or_top] type : either the resulting sets is small enough, or it is
    converted into an interval.

    Sets are always non-empty. The functions reducing the sets returns a
    [set or_bottom] type: either the result is non-empty, or it is `Bottom. *)

open Lattice_bounds

(** Returns the limit above which integer sets are converted into intervals. *)
val get_small_cardinal: unit -> int

(** Sets the limit above which integer sets are converted into intervals.
    This is used by the Eva plugin according to the -eva-ilevel option.
    Do not use. *)
val set_small_cardinal: int -> unit

include Datatype.S_with_collections

(** Creates the set containing only the given integer. *)
val inject_singleton: Integer.t -> t

(** Creates the set with integers [from + k*period] for [k] in
    [{0 ... number-1}]. The resulting set contains [number] integers. There is
    no verification about [number], but it should be stritly positive. *)
val inject_periodic: from:Integer.t -> period:Integer.t -> number:Integer.t -> t

(** Creates a set from an integer list. The list must not be empty, and the list
    length must not exceed the small cardinal limit. *)
val inject_list: Integer.t list -> t

(** Returns the set as an integer list. *)
val to_list: t -> Integer.t list

(** Removes an integer from a set.
    Returns Bottom if the resulting set is empty. *)
val remove: t -> Integer.t -> t or_bottom

(** [mem i s] is true iff the set [s] contains the integer [i]. *)
val mem: Integer.t -> t -> bool

val one: t
val zero: t
val minus_one: t
val zero_or_one: t

val min: t -> Integer.t (** Returns the smallest integer of a set. *)

val max: t -> Integer.t (** Returns the highest integer of a set. *)

(** Returns the number of integers in a set. *)
val cardinal: t -> int

(** {2 Iterators on the integers of a set.} *)

val for_all: (Integer.t -> bool) -> t -> bool
val exists: (Integer.t -> bool) -> t -> bool
val iter: (Integer.t -> unit) -> t -> unit
val fold: ?increasing:bool -> (Integer.t -> 'a -> 'a) -> t -> 'a -> 'a
val map: (Integer.t -> Integer.t) -> t -> t
val filter: (Integer.t -> bool) -> t -> t or_bottom
val map_reduce: (Integer.t -> 'a) -> ('a -> 'a -> 'a) -> t -> 'a

(** Sets whose cardinal exceeds a certain limit must be converted into
    intervals. Functions that make sets grow returns either a set small enough,
    or the information needed to construct the corresponding interval: the
    smallest and highest elements, and the periodicity of the integers of
    the set. *)
type set_or_top =
  [ `Set of t                                  (** Small set. *)
  | `Top of Integer.t * Integer.t * Integer.t  (** Interval: min, max, modu *)
  ]

type set_or_top_or_bottom = [ `Bottom | set_or_top ]

(** [apply2 f s1 s2] applies [f i1 i2] for all integers i1 in s1 and i2 in s2. *)
val apply2: (Integer.t -> Integer.t -> Integer.t) -> t -> t -> set_or_top

(** {2 Lattice structure.} *)

val is_included: t -> t -> bool
val join: t -> t -> set_or_top
val link: t -> t -> set_or_top
val meet: t -> t -> t or_bottom
val narrow: t -> t -> t or_bottom
val intersects: t -> t -> bool
val diff_if_one: t -> t -> t or_bottom
val complement_under:
  min:Integer.t -> max:Integer.t -> t -> set_or_top_or_bottom

(** {2 Semantics.} *)

(** See {!Int_val} for more details. *)

val add_singleton: Integer.t -> t -> t
val add: t -> t -> set_or_top
val add_under: t -> t -> set_or_top
val neg: t -> t
val abs: t -> t

val mul: t -> t -> set_or_top
val c_rem: t -> t -> set_or_top_or_bottom

val scale: Integer.t -> t -> t
val scale_div: pos:bool -> Integer.t -> t -> t
val scale_rem: pos:bool -> Integer.t -> t -> t

val bitwise_signed_not: t -> t

(** {2 Misc} *)

val subdivide: t -> t * t
