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

(** Access to other plugins API via {!Dynamic.get}. *)

module Callgraph: sig
  (** Iterates over all functions in the callgraph in reverse order, i.e. from
      callees to callers. If callgraph is missing, the order is unspecified. *)
  val iter_in_rev_order: (Kernel_function.t -> unit) -> unit

  (** Returns [true] if [base] is a global, or a formal or local of either [kf]
      or one of its callers. If callgraph is missing, always returns true. *)
  val accept_base: Kernel_function.t -> Base.t -> bool
end

module Scope: sig
  (** Removes redundant assertions. Warns if the scope plugin is missing. *)
  val rm_asserts: unit -> unit
end

module RteGen: sig
  (** Marks all RTE as generated. Does nothing if the rte plugin is missing. *)
  val mark_generated_rte: unit -> unit
end
