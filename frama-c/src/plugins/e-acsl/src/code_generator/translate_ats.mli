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

(** Generate C implementations of E-ACSL [\at()] terms and predicates. *)

open Cil_types
open Analyses_types

(**************************************************************************)
(*************************** Translation **********************************)
(**************************************************************************)

val for_stmt: Env.t -> kernel_function -> stmt -> Env.t
(** Translate all [\at()] predicates and terms for the given statement in the
    current environment. *)

val to_exp:
  loc:location ->
  adata:Assert.t ->
  kernel_function ->
  Env.t ->
  pred_or_term ->
  logic_label ->
  exp * Assert.t * Env.t
(** @return the C expression corresponding to the given [pred_or_term].

    The expression is either translated in-place or retrieved from a
    pre-translation phase. *)

val reset: unit -> unit
(** Clear the stored translations. *)

(*****************************************************************************)
(**************************** Handling memory ********************************)
(*****************************************************************************)

(* The different possible evaluations of the [\at] under study are
   stored in a memory location that needs to be allocated then freed.
   This part is designed for that purpose. *)

module Malloc: sig
  val find_all: kernel_function -> stmt list
  (** @return the list of [malloc] stmts that need to be inserted into [kf]. *)

  val remove_all: kernel_function -> unit
  (** Remove all [malloc] stmts for [kf] from the internal table. *)
end

module Free: sig
  val find_all: kernel_function -> stmt list
  (** @return the list of [free] stmts that need to be inserted into [kf]. *)

  val remove_all: kernel_function -> unit
  (** Remove all [free] stmts for [kf] from the internal table. *)
end

(**************************************************************************)
(********************** Forward references ********************************)
(**************************************************************************)

val term_to_exp_ref:
  (adata:Assert.t ->
   ?inplace:bool ->
   kernel_function ->
   Env.t ->
   term ->
   exp * Assert.t * Env.t) ref

val predicate_to_exp_ref:
  (adata:Assert.t ->
   ?inplace:bool ->
   ?name:string ->
   kernel_function ->
   ?rte:bool ->
   Env.t ->
   predicate ->
   exp * Assert.t * Env.t) ref

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
