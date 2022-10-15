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

(** This module defines the mode to restrict an abstract domain on specific
    functions. *)

(** Permission for an abstract domain to read/write its state.
    If [write] is true, the domain infers new properties when interpreting
    assignments, assumptions, and logical assertions. Otherwise, it only
    propagates already known properties as long as they hold.
    If [read] is true, the domain uses its inferred properties to improve
    the evaluation of expressions by extracting information from its state.
    It can also evaluate logical assertions. *)
type permission = { read: bool; write: bool; }

(** Mode for the analysis of a function [f]:
    - [current] is the read/write permission for [f].
    - [calls] is the read/write permission for all functions called from [f]. *)
type mode = { current: permission; calls: permission; }

(** Datatype for modes. *)
module Mode : sig
  include Datatype.S_with_collections with type t = mode
  val all: t (** Default mode: all permissions are granted. *)
end

(** A function associated with an analysis mode. *)
type function_mode = Kernel_function.t * mode

module Function_Mode:
  Parameter_sig.Multiple_value_datatype with type key = string
                                         and type t = function_mode

(** Analysis mode for a domain. *)
include Datatype.S with type t = function_mode list
