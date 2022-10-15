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

(** This module computes the set of kernel functions that are considered by
    the command line options transmitted to WP. That is:

    - all functions on which a verification must be tried,
    - all functions that are called by the previous ones,
    - including those parameterized via the 'calls' clause.

    It takes in account the options -wp-bhv and -wp-props so that if all
    functions are initially selected but in fact some of them are filtered out
    by these options, they are not considered.
*)

val compute: WpContext.model -> unit
val iter: (Kernel_function.t -> unit) -> unit


val with_callees: Kernel_function.t -> Kernel_function.Set.t
(** @returns the set composed of the given kernel_function together with its
    callees. If this function does not have a definition, the empty set is
    returned.
*)
