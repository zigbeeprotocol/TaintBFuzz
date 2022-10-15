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


(* Composition operator for compare function *)

let (<?>) c lcmp =
  if c = 0 then 0 else Lazy.force lcmp


(* Imprecise bits abstraction *)

type initialization =
  | SurelyInitialized
  | MaybeUninitialized

type bit =
  | Uninitialized
  | Zero of initialization
  | Any of Base.SetLattice.t * initialization

module Initialization =
struct
  let pretty fmt = function
    | SurelyInitialized -> ()
    | MaybeUninitialized ->
      Format.fprintf fmt "or UNINITIALIZED"

  let hash = function
    | SurelyInitialized -> 3
    | MaybeUninitialized -> 7

  let equal i1 i2 =
    match i1, i2 with
    | SurelyInitialized, SurelyInitialized
    | MaybeUninitialized, MaybeUninitialized -> true
    | _, _ -> false

  let compare i1 i2 =
    match i1, i2 with
    | SurelyInitialized, SurelyInitialized
    | MaybeUninitialized, MaybeUninitialized -> 0
    | SurelyInitialized, MaybeUninitialized -> -1
    | MaybeUninitialized, SurelyInitialized -> 1

  let is_included i1 i2 =
    match i1, i2 with
    | SurelyInitialized, _
    | _, MaybeUninitialized -> true
    | MaybeUninitialized, SurelyInitialized -> false

  let join i1 i2 =
    match i1, i2 with
    | SurelyInitialized, SurelyInitialized -> SurelyInitialized
    | MaybeUninitialized, _
    | _, MaybeUninitialized -> MaybeUninitialized
end

module Bit =
struct
  module Bases = Base.SetLattice

  type t = bit

  let uninitialized = Uninitialized
  let zero = Zero SurelyInitialized
  let numerical = Any (Bases.empty, SurelyInitialized)
  let top = Any (Bases.top, MaybeUninitialized)


  let pretty fmt = function
    | Uninitialized ->
      Format.fprintf fmt "UNINITIALIZED"
    | Zero i ->
      Format.fprintf fmt "0%a" Initialization.pretty i
    | Any (Set set, i) when Base.SetLattice.O.is_empty set ->
      Format.fprintf fmt "[--..--]%a" Initialization.pretty i
    | Any _ -> Format.fprintf fmt "T"

  let is_any = function Any _ -> true | _ -> false

  let hash = function
    | Uninitialized -> 7
    | Zero i -> Hashtbl.hash (3, Initialization.hash i)
    | Any (set, i)-> Hashtbl.hash (53, Bases.hash set, Initialization.hash i)

  let equal d1 d2 =
    match d1,d2 with
    | Uninitialized, Uninitialized -> true
    | Zero i1, Zero i2 -> Initialization.equal i1 i2
    | Any (set1,i1), Any (set2,i2) ->
      Bases.equal set1 set2 && Initialization.equal i1 i2
    | _, _ -> false

  let compare d1 d2 =
    match d1,d2 with
    | Uninitialized, Uninitialized -> 0
    | Zero i1, Zero i2 -> Initialization.compare i1 i2
    | Any (set1,i1), Any (set2,i2) ->
      Bases.compare set1 set2 <?> lazy (Initialization.compare i1 i2)
    | Uninitialized, _ -> 1
    | _, Uninitialized -> -1
    | Zero _, _ -> 1
    | _, Zero _-> -1

  let initialization = function
    | Uninitialized -> MaybeUninitialized
    | Zero i -> i
    | Any (_,i) -> i

  let is_included d1 d2 =
    Initialization.is_included (initialization d1) (initialization d2) &&
    match d1, d2 with
    | Uninitialized, _ -> true
    | _, Uninitialized -> false
    | Zero _, _ -> true
    | _, Zero _ -> false
    | Any (set1,_), Any (set2,_) -> Bases.is_included set1 set2

  let join d1 d2 =
    match d1, d2 with
    | Uninitialized, Uninitialized -> Uninitialized
    | Zero i1, Zero i2 ->
      Zero (Initialization.join i1 i2)
    | Any (set1,i1), Any (set2,i2) ->
      Any (Bases.join set1 set2, Initialization.join i1 i2)
    | Zero _, Uninitialized
    | Uninitialized, Zero _ -> Zero MaybeUninitialized
    | Any (set,i), (Zero _ | Uninitialized as b)
    | (Zero _ | Uninitialized as b), Any (set,i) ->
      Any (set, Initialization.join i (initialization b))
end


(* Early stage of memory abstraction building *)

type size = Integer.t
type side = Left | Right
type oracle = Cil_types.exp -> Int_val.t
type bioracle = side -> oracle

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
