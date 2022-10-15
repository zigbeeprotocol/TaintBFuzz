(**************************************************************************)
(*                                                                        *)
(*  This file is part of Aorai plug-in of Frama-C.                        *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*    INRIA (Institut National de Recherche en Informatique et en         *)
(*           Automatique)                                                 *)
(*    INSA  (Institut National des Sciences Appliquees)                   *)
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

(** visitors performing the instrumentation *)

module Aux_funcs: sig
  (** the various kinds of auxiliary functions. *)
  type kind =
    | Not_aux_func (** original C function. *)
    | Aux of Cil_types.kernel_function
    (** Checks whether we are in the corresponding behavior
        of the function. *)
    | Pre of Cil_types.kernel_function
    (** [Pre_func f] denotes a function updating the automaton
        when [f] is called. *)
    | Post of Cil_types.kernel_function
    (** [Post_func f] denotes a function updating the automaton
        when returning from [f]. *)

  val iter: (Cil_types.varinfo -> kind -> unit) -> unit
  (** [iter f] calls [f] on all functions registered so far by
      {!add_sync_with_buch}
  *)

end

(** generate prototypes for auxiliary functions. *)
val add_sync_with_buch: Cil_types.file -> unit

(**
   [add_pre_post_from_buch ast treatloop]
   provide contracts and/or bodies for auxiliary function
   (once they have been generated). If [treatloop] is [true],
   loop invariants are also generated.
*)
val add_pre_post_from_buch: Cil_types.file -> bool -> unit
