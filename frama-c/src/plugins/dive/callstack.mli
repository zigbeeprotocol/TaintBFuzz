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

type call_site = (Cil_types.kernel_function * Cil_types.kinstr)
type t = call_site list

include Datatype.S_with_collections with type t := t

(* The callstacks manipulated here have the following invariant:
   - the callstack is never an empty list
   - the last item of the list has always a Kglobal
   - all elements of the list except the last have a Kstmt *)

val init : Cil_types.kernel_function -> t
val pop : t -> (Cil_types.kernel_function * Cil_types.stmt * t) option
val pop_downto : Cil_types.kernel_function -> t -> t
val top_kf : t -> Cil_types.kernel_function
val push : Cil_types.kernel_function * Cil_types.stmt -> t -> t
val is_prefix : t -> t -> bool
val truncate_to_sub : t -> t -> t option
val filter_truncate : t list -> t -> t list
