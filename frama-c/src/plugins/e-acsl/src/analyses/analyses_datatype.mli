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

(** Datatypes for analyses types *)

open Cil_types
open Analyses_types

module Annotation_kind: Datatype.S with type t = annotation_kind

module Pred_or_term: Datatype.S_with_collections with type t = pred_or_term

module At_data: sig
  include Datatype.S_with_collections with type t = at_data

  val create:
    ?error:exn ->
    kernel_function ->
    kinstr ->
    lscope ->
    pred_or_term ->
    logic_label ->
    at_data
    (** [create ?error kf kinstr lscope pot label] creates an [at_data] from the
        given arguments. *)
end
