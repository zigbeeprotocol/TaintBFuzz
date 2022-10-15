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

(* Builds an environement to resolve names of globals and functions which
   can then be used, even if Frama-C global tables are not filled yet. *)

type t

val from_file : Cil_types.file -> t

val find_global : t -> string -> Cil_types.varinfo
val find_function : t -> string ->  Cil_types.varinfo
val find_typedef : t -> string ->  Cil_types.typeinfo
val find_struct : t -> string ->  Cil_types.compinfo
val find_union : t -> string ->  Cil_types.compinfo
val find_enum : t -> string ->  Cil_types.enuminfo
val find_type : t -> Logic_typing.type_namespace -> string -> Cil_types.typ
