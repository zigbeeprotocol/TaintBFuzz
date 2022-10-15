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
open Abstract_memory

module type Config =
sig
  (* Dependencies of the hash-consing table. The table will be cleared
     whenever one of those dependencies is cleared. *)
  val deps : State.t list
end

module type Structure =
sig
  type t
  type submemory
  val pretty : Format.formatter -> t -> unit
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val raw : t -> Bit.t
  val of_raw : Bit.t -> t
  val weak_erase : Bit.t -> t -> t
  val is_included : t -> t -> bool
  val unify : (submemory -> submemory -> submemory) -> t -> t -> t
  val read : t -> Cil_types.fieldinfo -> submemory
  val update : (submemory -> submemory or_bottom) -> t -> Cil_types.fieldinfo ->
    t or_bottom
  val map : (submemory -> submemory) -> t -> t
end

module Make (Config : Config) (M : ProtoMemory) :
  Structure with type submemory = M.t

module type Disjunction =
sig
  type t
  type submemory
  type structure
  val pretty : Format.formatter -> t -> unit
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val raw : t -> Bit.t
  val of_raw : Cil_types.compinfo -> Bit.t -> t
  val of_struct : Cil_types.compinfo -> structure -> t
  val to_struct : oracle:oracle -> t -> structure
  val weak_erase : Cil_types.compinfo -> Bit.t -> t -> t
  val is_included : t -> t -> bool
  val unify : oracle:bioracle -> (submemory -> submemory -> submemory) ->
    t -> t -> t
  val read : (submemory -> 'a) -> ('a -> 'a -> 'a)  ->
    t -> Cil_types.fieldinfo -> 'a
  val update : oracle:oracle -> (submemory -> submemory or_bottom) ->
    t -> Cil_types.fieldinfo -> t or_bottom
  val map : (submemory -> submemory) -> t -> t
end

module Disjunction (M : ProtoMemory) (S : Structure with type submemory = M.t) :
  Disjunction with type submemory = M.t and type structure = S.t
