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

(** Domain for a taint analysis. *)

include Abstract_domain.Leaf
  with type value = Cvalue.V.t
   and type location = Precise_locs.precise_location

val flag: Abstractions.flag

type taint_error =
  | NotComputed (** The Eva analysis has not been run, or the taint domain
                    was not enabled. *)
  | Irrelevant  (** Properties other than assertions, invariants and
                    preconditions are irrelevant here. *)
  | LogicError  (** The memory zone on which the property depends could not
                    be computed. *)

type taint_ok =
  | Data    (** Data-taint: there is a data dependency from the values provided
                by the attacker to the given property, meaning that the attacker
                may alter the values on which the property depends. *)
  | Control (** Control-taint: there is a control-dependency from the values
                provided by the attacker to the given property. The attacker
                cannot directly alter the values on which the property depends,
                but he may be able to choose the path where these values are
                computed. *)
  | None    (** No taint: the property cannot be altered by the attacker. *)

type taint_result = (taint_ok, taint_error) result

val is_tainted_property: Property.t -> taint_result
