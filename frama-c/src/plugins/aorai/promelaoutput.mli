(**************************************************************************)
(*                                                                        *)
(*  This file is part of Aorai plug-in of Frama-C.                        *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*    INRIA (Institut National de Recherche en Informatique et en         *)
(*           Automatique)                                                 *)
(*    INSA  (Institut National des Sciences Appliquees)                   *)
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

open Promelaast

type 'a printer = Format.formatter -> 'a -> unit

val print_state : state printer
val print_statel : state list printer

module Parsed:
sig
  val print_expression: expression printer
  val print_condition: condition printer
  val print_seq_elt: seq_elt printer
  val print_sequence: sequence printer
  val print_guard: guard printer
  val print_action: action printer
  val print_actionl: action list printer
end

module Typed:
sig
  val print_condition : typed_condition printer
  val print_action: typed_action printer
  val print_actionl: typed_action list printer
  val print_transition: typed_trans printer
  val print_transitionl: typed_trans list printer
  val print_automata : typed_automaton printer
  val output_dot_automata : typed_automaton -> string -> unit
end


(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
