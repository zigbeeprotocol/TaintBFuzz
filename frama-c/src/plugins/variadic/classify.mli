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

(** Checks if the given name is the name of a Frama-C builtin *)
val is_frama_c_builtin : string -> bool

(** Checks if the given name is the name of one of the variadic va_* builtins *)
val is_va_builtin : string -> bool

(** Checks if a varinfo is a variadic function *)
val is_variadic_function : Cil_types.varinfo -> bool

(** Build a variadic function record for the given [varinfo] according to its
    classification. Returns [None] if the function is not variadic. *)
val classify : Environment.t -> Cil_types.varinfo ->
  Va_types.variadic_function option
