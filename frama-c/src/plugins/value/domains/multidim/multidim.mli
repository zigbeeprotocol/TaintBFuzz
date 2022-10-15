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

(** [offset] is an abstraction for array indexes when these
    arrays are used as a representation of multidimensional arrays or
    structures. They have the form :

    o + d₁×[0,b₁]  + ... + dₙ×[0,bₙ]

    or, more formally

    \{ o + Σ dᵢ×xᵢ | ∀i 1≤i≤n ⇒ xᵢ ∊ [0, bᵢ] \}

    This is a generalisation of integers intervals with modulo implemented in
    Ival : o + d×[0, b]

    The list of dᵢ is sorted in descending order and we may add the constraint

    dᵢ×bᵢ < dᵢ₋₁

    which is verified for normal multidimensional arrays handling.
*)
type index = Integer.t * (Integer.t * Integer.t) list (* o, [dᵢ,bᵢ]ᵢ *)

include Datatype.S with type t = index

(* Constructors *)

val zero : t
val of_int : int -> t
val of_integer : Integer.t -> t
val of_ival : Ival.t -> t (* Raises Abstract_interp.Error_Bottom and Error_Top *)

(* Properties *)

val is_zero : t -> bool
val is_singleton : t -> bool
val hull : t -> Integer.t * Integer.t (* start * size *)

(* Decomposition *)

val first_dimension : t -> (Integer.t * t) option

(* Arithmetic *)

val add : t -> t -> t
(* slightly faster than add since no normalization takes place *)
val add_int : t -> int -> t
val add_integer : t -> Integer.t -> t
val sub_int : t -> int -> t
val sub_integer : t -> Integer.t -> t

val mul : t -> t -> t
val mul_int : t -> int -> t
val mul_integer : t -> Integer.t -> t

val mod_int : t -> int -> t
val mod_integer : t -> Integer.t -> t

(* Conversion from Cil *)

val of_exp : (Cil_types.exp -> t) -> Cil_types.exp -> t (* improves over an oracle *)
val of_offset : (Cil_types.exp -> t) -> Cil_types.typ -> Cil_types.offset -> t
