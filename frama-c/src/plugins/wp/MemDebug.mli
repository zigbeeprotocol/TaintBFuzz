(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(* --- Debug Memory Model                                                 --- *)
(* -------------------------------------------------------------------------- *)

val pp_sequence : 'a Pretty_utils.formatter -> Format.formatter ->
  'a Sigs.sequence -> unit
val pp_equation : Format.formatter -> Sigs.equation -> unit
val pp_acs : Format.formatter -> Sigs.acs -> unit
val pp_value : 'a Pretty_utils.formatter -> Format.formatter ->
  'a Sigs.value -> unit
val pp_rloc : 'a Pretty_utils.formatter -> Format.formatter ->
  'a Sigs.rloc -> unit
val pp_sloc : 'a Pretty_utils.formatter -> Format.formatter ->
  'a Sigs.sloc -> unit

module Make(M : Sigs.Model) : Sigs.Model
