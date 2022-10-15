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

(** Pre-analysis for Labeled terms and predicates.

    This pre-analysis records, for each labeled term or predicate, the place
    where the translation must happen.

    The list of labeled terms or predicates to be translated for a given
    statement is provided by [Labels.at_for_stmt]. *)

open Cil_types
open Analyses_datatype

val get_first_inner_stmt: stmt -> stmt
(** If the given statement has a label, return the first statement of the block.
    Otherwise return the given statement. *)

val at_for_stmt: stmt -> At_data.Set.t Error.result
(** @return the set of labeled predicates and terms to be translated on the
    given statement.
    @raise Not_memoized if the labels pre-analysis was not run. *)

val preprocess: file -> unit
(** Analyse sources to find the statements where a labeled predicate or term
    should be translated. *)

val reset: unit -> unit
(** Reset the results of the pre-anlaysis. *)

val _debug: unit -> unit
(** Print internal state of labels translation. *)

(**************************************************************************)
(********************** Forward references ********************************)
(**************************************************************************)

val has_empty_quantif_ref: ((term * logic_var * term) list -> bool) ref

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
