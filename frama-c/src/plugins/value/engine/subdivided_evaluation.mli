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

(** Subdivision of the evaluation on non-linear expressions:
    for expressions in which some l-values appear multiple times, proceed
    by disjunction on their abstract value, in order to gain precision. *)

open Cil_types
open Eval

module type Forward_Evaluation = sig
  type value
  type valuation
  type context
  val evaluate: subdivided:bool -> context -> valuation ->
    exp -> (valuation * value) evaluated
end

module Make
    (Value : Abstract.Value.External)
    (Loc: Abstract_location.S with type value = Value.t)
    (Valuation: Valuation with type value = Value.t
                           and type loc = Loc.location)
    (Eva: Forward_Evaluation with type value := Value.t
                              and type valuation := Valuation.t)
  : sig

    val evaluate:
      Eva.context -> Valuation.t -> subdivnb:int ->
      exp -> (Valuation.t * Value.t) evaluated

    val reduce_by_enumeration:
      Eva.context -> Valuation.t -> exp -> bool -> Valuation.t or_bottom
  end


(*
Local Variables:
compile-command: "make -C ../../../.."
End:
*)
