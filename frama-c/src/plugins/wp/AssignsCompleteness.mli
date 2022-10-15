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

(** This module is used to check the assigns specification of a given function
    so that if it is not precise enough to enable precise memory models
    hypotheses computation, the assigns specification is considered incomplete.

    All these functions are memoized.
*)

val compute: Kernel_function.t -> unit

val is_complete: Kernel_function.t -> bool

val warn: Kernel_function.t -> unit
(** Displays a warning if the given kernel function has incomplete assigns.
    Note that the warning is configured with [~once] set to [true]. *)

val wkey_pedantic: Wp_parameters.warn_category
