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

(** Utilities for E-ACSL. *)

open Cil_types

(* ************************************************************************** *)
(** {2 Handling \result} *)
(* ************************************************************************** *)

val result_lhost: kernel_function -> lhost
(** @return the lhost corresponding to \result in the given function *)

val result_vi: kernel_function -> varinfo
(** @return the varinfo corresponding to \result in the given function *)

(* ************************************************************************** *)
(** {2 Other stuff} *)
(* ************************************************************************** *)

val is_fc_or_compiler_builtin: varinfo -> bool

val is_fc_stdlib_generated: varinfo -> bool
(** Returns true if the [varinfo] is a generated stdlib function. (For instance
    generated function by the Variadic plug-in. *)

val cty: logic_type -> typ
(** Assume that the logic type is indeed a C type. Just return it. *)

val ptr_base: loc:location -> exp -> exp
(** Takes an expression [e] and return [base] where [base] is the address [p]
    if [e] is of the form [p + i] and [e] otherwise. *)

val ptr_base_and_base_addr: loc:location -> exp -> exp * exp
(* Takes an expression [e] and return a tuple [(base, base_addr)] where [base]
   is the address [p] if [e] is of the form [p + i] and [e] otherwise, and
   [base_addr] is the address [&p] if [e] is of the form [p + i] and 0
   otherwise. *)

val term_of_li: logic_info -> term
(** [term_of_li li] assumes that [li.l_body] matches [LBterm t]
    and returns [t]. *)

val is_set_of_ptr_or_array: logic_type -> bool
(** Checks whether the given logic type is a set of pointers. *)

val is_range_free: term -> bool
(** @return true iff the given term does not contain any range. *)

val is_bitfield_pointers: logic_type -> bool
(** @return true iff the given logic type is a bitfield pointer or a
    set of bitfield pointers. *)

val term_has_lv_from_vi: term -> bool
(** @return true iff the given term contains a variables that originates from
    a C varinfo, that is a non-purely logic variable. *)

val name_of_binop: binop -> string
(** @return the name of the given binop as a string. *)

val finite_min_and_max: Ival.t -> Integer.t * Integer.t
(** [finite_min_and_max i] takes the finite ival [i] and returns its bounds. *)

module Id_term: Datatype.S_with_collections with type t = term
(** Datatype for terms that relies on physical equality. *)

val extract_uncoerced_lval: exp -> exp option
(** Unroll the [CastE] part of the expression until an [Lval] is found, and
    return it.

    If at some point the expression is neither a [CastE] nor an [Lval], then
    return [None]. *)

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
