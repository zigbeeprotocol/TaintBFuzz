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

(* Create calls to a few memory built-ins.
   Partial support for ranges is provided. *)

val call:
  adata:Assert.t ->
  loc:location ->
  kernel_function ->
  string ->
  typ ->
  Env.t ->
  term ->
  exp * Assert.t * Env.t
(* [call ~loc kf name ctx env t] creates a call to the E-ACSL memory built-in
   identified by [name] which only requires a single argument, namely the
   pointer under study. The supported built-ins are:
   [base_addr], [block_length], [offset] and [freeable]. *)

val call_with_size:
  adata:Assert.t ->
  loc:location ->
  kernel_function ->
  string ->
  typ ->
  Env.t ->
  term list ->
  predicate ->
  exp * Assert.t * Env.t
(* [call_with_size ~loc kf name ctx env tlist p] creates a call to the E-ACSL
   memory built-in identified by [name] which requires two arguments per term,
   namely the pointer under study and a size in bytes.
   The supported built-ins are: [initialized] and [separated].
   Each term in [tlist] can denote ranges of memory locations.
   [p] is the predicate under testing. *)

val call_valid:
  adata:Assert.t ->
  loc:location ->
  kernel_function ->
  string ->
  typ ->
  Env.t ->
  term ->
  predicate ->
  exp * Assert.t * Env.t
(* [call_valid ~loc kf name ctx env t p] creates a call to the E-ACSL memory
   built-in [valid] or [valid_read] according to [name].
   [t] can denote ranges of memory locations.
   [p] is the predicate under testing. *)

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

val gmp_to_sizet_ref:
  (adata:Assert.t ->
   loc:location ->
   name:string ->
   ?check_lower_bound:bool ->
   ?pp:term ->
   kernel_function ->
   Env.t ->
   term ->
   exp * Assert.t * Env.t) ref
