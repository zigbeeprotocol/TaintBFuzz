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

open Cil_types

type validity = Valid | Nullable
type param = NotUsed | ByAddr | ByValue | ByShift | ByRef
           | InContext of validity | InArray of validity

val pp_param: Format.formatter -> param -> unit

type partition

val empty: partition
val set: varinfo -> param -> partition -> partition

val compute: string -> (kernel_function -> partition) -> unit

val add_behavior:
  kernel_function -> string -> (kernel_function -> partition) -> unit
val warn:
  kernel_function -> string -> (kernel_function -> partition) -> unit
