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

(** Utility functions for generating C implementations. *)

val must_translate: Property.t -> bool
(** @return true if the given property must be translated (ie. if the valid
    properties must be translated or if its status is not [True]), false
    otherwise. *)

val must_translate_opt: Property.t option -> bool
(** Same than [must_translate] but for [Property.t option]. Return false if the
    option is [None]. *)

val gmp_to_sizet:
  adata:Assert.t ->
  loc:location ->
  name:string ->
  ?check_lower_bound:bool ->
  ?pp:term ->
  kernel_function ->
  Env.t ->
  term ->
  exp * Assert.t * Env.t
(** Translate the given GMP integer to an expression of type [size_t]. RTE
    checks are generated to ensure that the GMP value holds in this type.
    The parameter [name] is used to generate relevant predicate names.
    If [check_lower_bound] is set to [false], then the GMP value is assumed to
    be positive.
    If [pp] is provided, this term is used in the messages of the RTE checks. *)

val comparison_to_exp:
  adata:Assert.t ->
  loc:location ->
  kernel_function ->
  Env.t ->
  Typing.number_ty ->
  ?e1:exp ->
  binop ->
  term ->
  term ->
  ?name:string ->
  term option ->
  exp * Assert.t * Env.t
(** [comparison_to_exp ~data ~loc kf env ity ?e1 ?name bop t1 t2 topt] generates
    the C code equivalent to [t1 bop t2] in the given environment with the
    given assertion context.
    [ity] is the number type of the comparison when comparing scalar numbers.
    [e1] is the expression representing [t1] if the term has already been
    translated.
    [name] is used to generate temporary variable names.
    [topt] is the term holding the result of the comparison. *)

val conditional_to_exp:
  ?name:string ->
  loc:location ->
  kernel_function ->
  term option ->
  exp ->
  exp * Env.t ->
  exp * Env.t ->
  exp * Env.t
(** [conditional_to_exp ?name ~loc kf t_opt e1 (e2, env2) (e3, env3)] generates
    the C code equivalent to [e1 ? e2 : e3] in the given  environment.
    [env2] and [env3] are the environment respectively for [e2] and [e3].
    [t_opt] is the term holding the result of the conditional. *)

val env_of_li:
  adata:Assert.t ->
  loc:location ->
  kernel_function ->
  Env.t ->
  logic_info ->
  Assert.t * Env.t
(** [env_of_li ~adata ~loc kf env li] translates the logic info [li] in the
    given environment with the given assertion context. *)

(**************************************************************************)
(********************** Forward references ********************************)
(**************************************************************************)

val term_to_exp_ref:
  (adata:Assert.t ->
   kernel_function ->
   Env.t ->
   term ->
   exp * Assert.t * Env.t) ref

val predicate_to_exp_ref:
  (adata:Assert.t ->
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
