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

(** Manipulate the type of numbers. *)

open Cil_types

(** Type of a string that represents a number.
    Used when a string is required to encode a constant number because it is not
    representable in any C type  *)
type strnum =
  | Str_Z         (* integers *)
  | Str_R         (* reals *)
  | C_number      (* integers and floats included *)

(** [add_cast ~loc ?name env kf ctx sty t_opt e] convert number expression [e]
    in a way that it is compatible with the given typing context [ctx].
    [sty] indicates if the expression is a string representing a number (integer
    or real) or directly a C number type.
    [t_opt] is the term that is represented by the expression [e]. *)
val add_cast:
  loc:location ->
  ?name:string ->
  Env.t ->
  kernel_function ->
  typ option ->
  strnum ->
  term option ->
  exp ->
  exp * Env.t
