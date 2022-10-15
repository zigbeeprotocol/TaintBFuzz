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
(* --- Array Dimensions                                                   --- *)
(* -------------------------------------------------------------------------- *)

type t (** Matrix dimensions.
           Encodes the number of dimensions and their kind *)

val of_dims : int option list -> t
val compare : t -> t -> int
val pretty : Format.formatter -> t -> unit
val pp_suffix_id : Format.formatter -> t -> unit

val merge : int option list -> int option list -> int option list option

open Lang.F

type env = {
  size_var : var list ; (** size variables *)
  size_val : term list ; (** size values *)
  index_var : var list ; (** index variables *)
  index_val : term list ; (** index values *)
  index_range : pred list ; (** indices are in range of size variables *)
  index_offset : term list ; (** polynomial of indices *)
  length : term option ; (** number of cells (None is infinite) *)
}

val cc_tau : tau -> t -> tau
(** Type of matrix *)

val cc_env : t -> env
(** Dimension environment *)

val cc_dims : int option list -> term list
(** Value of size variables *)

(* -------------------------------------------------------------------------- *)
