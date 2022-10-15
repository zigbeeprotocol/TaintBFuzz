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
open Eval

module Make
    (Abstract: Abstractions.S)
    (States: Powerset.S with type state = Abstract.Dom.t)
    (Logic : Transfer_logic.S with type state = Abstract.Dom.t
                               and type states = States.t)
  : sig

    val treat_statement_assigns: assigns -> Abstract.Dom.t -> Abstract.Dom.t

    val compute_using_specification:
      warn:bool ->
      kinstr -> (Abstract.Loc.location, Abstract.Val.t) call -> spec ->
      Abstract.Dom.t -> (Partition.key*Abstract.Dom.t) list

  end
