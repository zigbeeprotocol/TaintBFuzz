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

(** Handling of recursion cycles in the callgraph *)

open Cil_types
open Eval

(* Returns the specification for a recursive call to the given function. Fails
   if the function has no specification. Marks the preconditions of the call
   as unknowns. *)
val get_spec: kinstr -> kernel_function -> funspec

(** Creates the information about a recursive call. *)
val make: ('v, 'loc) call -> recursion option

(** Changes the information about a recursive call to be used at the end
    of the call. *)
val revert: recursion -> recursion
