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

(** Extend the environment with statements which allocate/deallocate memory
    blocks. *)

open Cil_types
open Cil_datatype

val store: Env.t -> kernel_function -> varinfo list -> Env.t
(** For each variable of the given list, if necessary according to the mtracking
    analysis, add a call to [__e_acsl_store_block] in the given environment. *)

val duplicate_store: Env.t -> kernel_function -> Varinfo.Set.t -> Env.t
(** Same as [store], with a call to [__e_acsl_duplicate_store_block]. *)

val delete_from_list: Env.t -> kernel_function -> varinfo list -> Env.t
(** Same as [store], with a call to [__e_acsl_delete_block]. *)

val delete_from_set: Env.t -> kernel_function -> Varinfo.Set.t -> Env.t
(** Same as [delete_from_list] with a set of variables instead of a list. *)

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
