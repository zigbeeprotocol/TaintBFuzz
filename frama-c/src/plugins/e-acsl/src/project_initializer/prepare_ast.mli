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

(** Prepare AST for E-ACSL generation.

    More precisely, this module performs the following tasks:
    - generating a new definition for functions with contract;
    - removing term sharing;
    - in case of temporal validity checks, adding the attribute "aligned" to
      variables that are not sufficiently aligned;
    - create a block around a labeled statement to hold the labels so that the
      code generation does not need to change the statement holding the label.
*)

open Cil_types

val prepare: unit -> unit
(** Prepare the AST *)

val sound_verdict: unit -> varinfo
(** @return the [varinfo] representing the E-ACSL global variable that indicates
    whether the verdict emitted by E-ACSL is sound. *)

(**************************************************************************)
(********************** Forward references ********************************)
(**************************************************************************)

val is_libc_writing_memory_ref: (varinfo -> bool) ref

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
