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

(** Server Plugin & Options *)

include Plugin.General_services

(** Generate documentation *)
module Doc : Parameter_sig.Filepath

(** Idle waiting time (in ms) *)
module Polling : Parameter_sig.Int

(** Monitor logs *)
module AutoLog : Parameter_sig.Bool

val wpage : warn_category
(** Inconsistent page warning *)

val wkind : warn_category
(** Inconsistent category warning *)

val wname : warn_category
(** Invalid name warning *)

val has_relative_filepath: unit -> bool

(**************************************************************************)
