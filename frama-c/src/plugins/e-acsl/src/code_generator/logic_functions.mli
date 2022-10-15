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

(** Generate C implementations of user-defined logic functions.
    A logic function can have multiple C implementations depending on
    the types computed for its arguments.
    Eg: Consider the following definition: [integer g(integer x) = x]
      with the following calls: [g(5)] and [g(10*INT_MAX)]
      They will respectively generate the C prototypes [int g_1(int)]
      and [long g_2(long)] *)

(**************************************************************************)
(************** Logic functions without labels ****************************)
(**************************************************************************)

val reset: unit -> unit

val app_to_exp:
  adata:Assert.t ->
  loc:location ->
  ?tapp:term ->
  kernel_function ->
  Env.t ->
  ?eargs:exp list ->
  logic_info ->
  term list ->
  exp * Assert.t * Env.t
(** Translate a Tapp term or a Papp predicate to an expression. If the optional
    argument [eargs] is provided, then these expressions are used as arguments
    of the fonction. The optional argument [tapp] is the term corresponding to
    the call, in case we are translating a term *)

val add_generated_functions: global list -> global list
(* @return the input list of globals in which the generated functions have been
   inserted at the right places (both their declaration and their definition) *)

(**************************************************************************)
(********************** Forward references ********************************)
(**************************************************************************)

val predicate_to_exp_ref:
  (adata:Assert.t ->
   kernel_function ->
   Env.t ->
   predicate ->
   exp * Assert.t * Env.t) ref

val term_to_exp_ref:
  (adata:Assert.t ->
   kernel_function ->
   Env.t ->
   term ->
   exp * Assert.t * Env.t) ref

(*
Local Variables:
compile-command: "make -C ../.."
End:
*)
