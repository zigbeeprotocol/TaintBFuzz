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

include Plugin.General_services

(** Instantiate transformation enabled *)
module Enabled : Parameter_sig.Bool

(** Set of kernel function provided for transformation *)
module Kfs : Parameter_sig.Kernel_function_set

(** Used by [Instantiator_builder] to generate options. For a given instantiator
    the module generates an option "-instantiate-(no-)<function_name>" that defaults
    to true.
*)
module NewInstantiator
    (B : sig val function_name: string end) : Parameter_sig.Bool

val emitter: Emitter.t
