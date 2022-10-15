(**************************************************************************)
(*                                                                        *)
(*  This file is part of the Frama-C's E-ACSL plug-in.                    *)
(*                                                                        *)
(*  Copyright (C) 2012-2021                                               *)
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

(** Observation of global variables. *)

open Cil_types

val function_init_name: string
(** Name of the function in which [mk_init_function] (see below) generates the
    code. *)

val function_clean_name: string
(** Name of the function in which [mk_clean_function] (see below) generates the
    code. *)

val reset: unit -> unit
val is_empty: unit -> bool

val add: varinfo -> unit
(** Observe the given variable if necessary. *)

val add_initializer: varinfo -> offset -> init -> unit
(** Add the initializer for the given observed variable. *)

val mk_init_function: unit -> varinfo * fundec
(** Generate a new C function containing the observers for global variable
    declarations and initializations. *)

val mk_clean_function: unit -> (varinfo * fundec) option
(** Generate a new C function containing the observers for global variable
    de-allocations if there are global variables. *)

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
