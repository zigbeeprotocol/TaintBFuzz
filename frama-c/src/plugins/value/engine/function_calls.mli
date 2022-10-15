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

(** True if the results should be saved for the given function. *)
val save_results: fundec -> bool

(** True if some results are not stored due to options -eva-no-results
    or -eva-no-results-function. *)
val partial_results: unit -> bool

(** What is used for the analysis of a given function:
    - a Cvalue builtin (and other domains use the specification)
    - the function specification
    - the function body. The boolean indicates whether the resulting states
      must be recorded at each statement of this function. *)
type analysis_target =
  [ `Builtin of string * Builtins.builtin * Eval.cacheable * funspec
  | `Spec of Cil_types.funspec
  | `Def of Cil_types.fundec * bool ]

(** Define the analysis target of a function according to Eva parameters.
    Also registers the call in tables for the functions below. *)
val define_analysis_target:
  ?recursion_depth:int -> kinstr -> kernel_function -> analysis_target

(** Returns true if the Eva analysis use the specification of the given
    function instead of its body to interpret its calls. *)
val use_spec_instead_of_definition:
  ?recursion_depth:int -> kernel_function -> bool


(** Returns true if the function has been analyzed. *)
val is_called: kernel_function -> bool

(** Returns the list of inferred callers of the given function. *)
val callers : Cil_types.kernel_function -> Cil_types.kernel_function list

(** Returns the list of inferred callers, and for each of them, the list
    of callsites (the call statements) inside. *)
val callsites: kernel_function -> (kernel_function * stmt list) list


type results = Complete | Partial | NoResults
type analysis_status =
    Unreachable | SpecUsed | Builtin of string | Analyzed of results

(** Returns the current analysis status of a given function. *)
val analysis_status: kernel_function -> analysis_status

(** The functions below are used by Eva_results.ml to save, merge and load
    the results of multiple Eva analyses.  *)

type t
val get_results: unit -> t
val set_results: t -> unit
val merge_results: t -> t -> t
