(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
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

type kind = CPtr | Ptr | Data of typ
type action = Strip | Id
type param = string * kind * action
type proto = kind * param list

module type Function = sig
  val name: string

  val prototype: unit -> proto

  (** receives the type of the lvalue and the types of the arguments received
      for a call to the function and returns [true] iff they are correct.
      The received types depend on the [prototype] of the module.
      - if the kind is [Data t] -> it is the exact type of the expr/lvalue
      - it the kind is [(C)Ptr] -> it is the pointed type of the expr/lvalue
  *)
  val well_typed: typ option -> typ list -> bool
end

module Make (F: Function) : sig
  val generate_function_type : typ -> typ
  val generate_prototype : typ -> string * typ
  val well_typed_call : lval option -> varinfo -> exp list -> bool
  val retype_args : typ -> exp list -> exp list
  val key_from_call : lval option -> varinfo -> exp list ->  typ
end

(** location -> key -> s1 -> s2 -> len -> spec_result *)
type 'a spec_gen = location -> typ -> term -> term -> term -> 'a

val mem2s_spec:
  requires: (identified_predicate list) spec_gen ->
  assigns: assigns spec_gen ->
  ensures: (termination_kind * identified_predicate) list spec_gen ->
  typ -> location -> fundec -> funspec

val mem2s_typing: typ option -> typ list -> bool

val memcpy_memmove_common_requires: (identified_predicate list) spec_gen

val memcpy_memmove_common_assigns: assigns spec_gen

val memcpy_memmove_common_ensures:
  string -> (termination_kind * identified_predicate) list spec_gen

type pointed_expr_type =
  | Of_null of typ
  | Value_of of typ
  | No_pointed

val exp_type_of_pointed: exp -> pointed_expr_type
