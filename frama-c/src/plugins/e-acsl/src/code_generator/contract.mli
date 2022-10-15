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
open Contract_types

(** Translate a given ACSL contract (function or statement) into the
    corresponding C statement for runtime assertion checking. *)

type t = contract

val create: loc:location -> spec -> t
(** Create a contract from a [spec] object (either function spec or statement
    spec) *)

val translate_preconditions: kernel_function -> Env.t -> t -> Env.t
(** Translate the preconditions of the given contract into the environement *)

val translate_postconditions: kernel_function -> Env.t -> Env.t
(** Translate the postconditions of the given contract into the environment *)
