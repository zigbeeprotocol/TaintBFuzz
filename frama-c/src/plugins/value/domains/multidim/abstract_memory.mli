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

open Lattice_bounds

(* Memory initialization *)
type initialization =
  | SurelyInitialized
  | MaybeUninitialized

(* Abstraction of an unstructured bit in the memory *)
type bit =
  | Uninitialized (* Uninitialized everywhere *)
  | Zero of initialization (* Zero or uninitialized everywhere *)
  | Any of Base.SetLattice.t * initialization
  (* Undetermined anywhere, and can contain bits
     of pointers. If the base set is empty,
     the bit can only come from numerical values. *)

module Bit :
sig
  type t = bit

  val uninitialized : t
  val zero : t
  val numerical : t
  val top : t

  val is_any : t -> bool
  val initialization : t -> initialization

  val pretty : Format.formatter -> t -> unit
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int

  val is_included : t -> t -> bool
  val join : t -> t -> t
end

(* Size type for memory abstraction *)
type size = Integer.t

(* Oracles for memory abstraction *)
type side = Left | Right
type oracle = Cil_types.exp -> Int_val.t
type bioracle = side -> oracle

(* Early stage of memory abstraction building *)
module type ProtoMemory =
sig
  type t
  type value

  val pretty : Format.formatter -> t -> unit
  val pretty_root : Format.formatter -> t -> unit
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int

  val of_raw : bit -> t
  val raw : t -> bit
  val of_value : Cil_types.typ -> value -> t
  val to_value : Cil_types.typ -> t -> value
  val to_singleton_int : t -> Integer.t option
  val weak_erase : bit -> t -> t
  val is_included : t -> t -> bool
  val unify : oracle:bioracle ->
    (size:size -> value -> value -> value) -> t -> t -> t
  val join : oracle:bioracle -> t -> t -> t
  val smash : oracle:oracle -> t -> t -> t
  val read : oracle:oracle -> (Cil_types.typ -> t -> 'a) -> ('a -> 'a -> 'a) ->
    Abstract_offset.t -> t -> 'a
  val update : oracle:oracle ->
    (weak:bool -> Cil_types.typ -> t -> t or_bottom) ->
    weak:bool -> Abstract_offset.t -> t -> t or_bottom
  val incr_bound : oracle:oracle -> Cil_types.varinfo -> Integer.t option ->
    t -> t
  val add_segmentation_bounds : oracle:oracle -> typ:Cil_types.typ ->
    Cil_types.exp list -> t -> t
end
