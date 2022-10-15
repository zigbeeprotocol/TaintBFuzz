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

val are_typ_compatible : Cil_types.typ -> Cil_types.typ -> bool


(* Configuration of the Abstract Memory model *)
module type Config =
sig
  (* Dependencies of the hash-consing table. The table will be cleared
     whenever one of those dependencies is cleared. *)
  val deps : State.t list

  (* Limit on the number of slice after a write for array segmentations.
     Makes sense above or equal to 1, though below 3 is counter-productive. *)
  val slice_limit : unit -> int

  (* Whether the memory model try to infer some structure disjunctive
     invariants. *)
  val disjunctive_invariants : unit -> bool
end

(* Values the memory is mapped to *)
module type Value =
sig
  type t

  val name : string

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int

  val pretty : Format.formatter -> t -> unit
  val of_bit : typ:Cil_types.typ -> bit -> t
  val to_bit : t -> bit
  val to_integer : t -> Integer.t option
  val is_included : t -> t -> bool
  val join : t -> t -> t
end

module Make (Config : Config) (Value : Value) :
sig
  type location = Abstract_offset.t
  type value = Value.t
  type t

  (* Datatype *)
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int

  (* Infinite unknown memory *)
  val top : t

  (* Infinite zero memory *)
  val zero : t

  (* Is the memory map completely unknown ? *)
  val is_top : t -> bool

  (* Get a value from a set of locations *)
  val get : oracle:oracle -> t -> location -> value

  (* Extract a sub map from a set of locations *)
  val extract : oracle:oracle -> t -> location -> t

  (* Erase / initialize the memory on a set of locations. *)
  val erase : oracle:oracle -> weak:bool -> t -> location -> bit -> t

  (* Set a value on a set of locations *)
  val set : oracle:oracle -> weak:bool -> t -> location -> value -> t

  (* Copy a whole map over another *)
  val overwrite : oracle:oracle -> weak:bool -> t -> location -> t -> t

  (* Reinforce values on a set of locations when the locations match the
     memory structure ; does nothing on locations that cannot be matched *)
  val reinforce : oracle:oracle ->
    (value -> value or_bottom) ->  t -> location -> t or_bottom

  (* Test inclusion of one memory map into another *)
  val is_included : t -> t -> bool

  (* Finest partition that is coarcer than both *)
  val join : oracle:bioracle -> t -> t -> t

  (* Partition widening *)
  val widen : oracle:bioracle -> (size:size -> value -> value -> value) ->
    t -> t -> t

  (* Bounds update for array segmentations *)
  val incr_bound : oracle:oracle -> Cil_types.varinfo -> Integer.t option ->
    t -> t

  (* Pretty prints memory *)
  val pretty : Format.formatter -> t -> unit

  (* Update the array segmentation at the given offset so the given bound
     expressions appear in the segmentation *)
  val segmentation_hint : oracle:oracle ->
    t -> location -> Cil_types.exp list -> t
end
