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

open Cil_types

(** Generate C implementations of E-ACSL terms. *)

val to_exp:
  adata:Assert.t ->
  ?inplace:bool ->
  kernel_function ->
  Env.t ->
  term ->
  exp * Assert.t * Env.t
(** [to_exp ~adata ?inplace kf env t] converts an ACSL term into a
    corresponding C expression.
    - [adata]: assertion context.
    - [inplace]: if the root term has a label, indicates if it should be
      immediately translated or if [Translate_ats] should be used to retrieve
      the translation.
    - [kf]: The enclosing function.
    - [env]: The current environment.
    - [t]: The term to translate. *)

exception No_simple_translation of term
(** Exceptin raised if [untyped_to_exp] would generate new statements in
    the environment *)

val untyped_to_exp: typ option -> term -> exp
(** Convert an untyped ACSL term into a corresponding C expression. *)

(**************************************************************************)
(********************** Forward references ********************************)
(**************************************************************************)

val translate_rte_exp_ref:
  (?filter:(code_annotation -> bool) ->
   kernel_function ->
   Env.t ->
   exp ->
   Env.t) ref

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
