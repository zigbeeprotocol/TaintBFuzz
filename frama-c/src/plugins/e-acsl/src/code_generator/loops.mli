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

(** Loop specific actions. *)

open Cil_types
open Analyses_types

(**************************************************************************)
(************************* Loop annotations *******************************)
(**************************************************************************)

val handle_annotations:
  Env.t -> Kernel_function.t -> stmt -> stmt * Env.t
(** Modify the given stmt loop to insert the code which verifies the loop
    annotations, ie. preserves its loop invariants and checks the loop variant.
    Also return the modified environment. *)

(**************************************************************************)
(**************************** Nested loops ********************************)
(**************************************************************************)

val mk_nested_loops:
  loc:location -> (Env.t -> stmt list * Env.t) -> kernel_function -> Env.t ->
  lscope_var list -> stmt list * Env.t
(** [mk_nested_loops ~loc mk_innermost_block kf env lvars] creates nested
    loops (with the proper statements for initializing the loop counters)
    from the list of logic variables [lvars]. Quantified variables create
    loops while let-bindings simply create new variables.
    The [mk_innermost_block] closure creates the statements of the innermost
    block. *)

(**************************************************************************)
(********************** Forward references ********************************)
(**************************************************************************)

val translate_predicate_ref:
  (kernel_function -> Env.t -> toplevel_predicate -> Env.t) ref

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
