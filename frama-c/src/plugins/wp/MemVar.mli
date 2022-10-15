(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(* --- No-Aliasing Memory Model                                           --- *)
(* -------------------------------------------------------------------------- *)

open Cil_types

module type VarUsage =
sig
  val datatype : string
  val param : varinfo -> MemoryContext.param
  val iter: ?kf:kernel_function -> init:bool -> (varinfo -> unit) -> unit

end

(** VarUsage naive instance.
    It reports a by-value access for all variables. *)
module Raw : VarUsage

(** VarUsage that uses only Cil-Static infos. *)
module Static : VarUsage

(** Create a mixed Hoare Memory Model from VarUsage instance. *)
module Make(V : VarUsage)(M : Sigs.Model) : Sigs.Model
