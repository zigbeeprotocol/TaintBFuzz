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

type t =
  | NoOffset of Cil_types.typ
  | Index of Cil_types.exp option * Int_val.t * Cil_types.typ * t
  | Field of Cil_types.fieldinfo * t

val pretty : Format.formatter -> t -> unit

val of_var_address : Cil_types.varinfo -> t
val of_cil_offset : (Cil_types.exp -> Int_val.t) ->
  Cil_types.typ -> Cil_types.offset -> t or_top
val of_ival : base_typ:Cil_types.typ -> typ:Cil_types.typ -> Ival.t -> t or_top
val of_term_offset : Cil_types.typ -> Cil_types.term_offset -> t or_top

val is_singleton : t -> bool
val references : t -> Cil_datatype.Varinfo.Set.t (* variables referenced in the offset *)

val append : t -> t -> t (* Does not check that the appened offset fits *)
val join : t -> t -> t or_top
val add_index : (Cil_types.exp -> Int_val.t) -> t -> Cil_types.exp -> t or_top
