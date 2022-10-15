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

(* ********************************************************************** *)
(* Helper functions to build expressions *)
(* ********************************************************************** *)

val lval: loc:location -> lval -> exp
(** Construct an lval expression from an lval. *)

val deref: loc:location -> exp -> exp
(** Construct a dereference of an expression. *)

val subscript: loc:location -> exp -> exp -> exp
(** [mk_subscript ~loc array idx] Create an expression to access the [idx]'th
    element of the [array]. *)

val ptr_sizeof: loc:location -> typ -> exp
(** [ptr_sizeof ~loc ptr_typ] takes the pointer typ [ptr_typ] that points
    to a [typ] typ and returns [sizeof(typ)]. *)

val lnot: loc:location -> exp -> exp
(** [lnot ~loc e] creates a logical not on the given expression [e]. *)

val null: loc:location -> exp
(** [null ~loc] creates an expression to represent the NULL pointer. *)

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
