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

open Cil_types

val valid_size: ?loc:location -> typ -> term -> identified_predicate

val is_allocable: ?loc:location -> term -> identified_predicate
val isnt_allocable: ?loc:location -> term -> identified_predicate

val assigns_result: ?loc:location -> typ -> term list -> from
val assigns_heap: term list -> from

val allocates_nothing: unit -> allocation
val allocates_result: ?loc:location -> typ -> allocation

val fresh_result: ?loc:location -> typ -> term -> identified_predicate
val null_result: ?loc:location -> typ -> identified_predicate
