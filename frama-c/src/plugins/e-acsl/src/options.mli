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

include Plugin.S (** implementation of Log.S for E-ACSL *)

module Run: Parameter_sig.Bool
module Valid: Parameter_sig.Bool
module Gmp_only: Parameter_sig.Bool
module Full_mtracking: Parameter_sig.Bool
module Project_name: Parameter_sig.String
module Builtins: Parameter_sig.String_set
module Temporal_validity: Parameter_sig.Bool
module Validate_format_strings: Parameter_sig.Bool
module Replace_libc_functions: Parameter_sig.Bool
module Assert_print_data: Parameter_sig.Bool
module Concurrency: Parameter_sig.Bool

module Functions: Parameter_sig.Kernel_function_set
module Instrument: Parameter_sig.Kernel_function_set

val parameter_states: State.t list
val emitter: Emitter.t

val must_visit: unit -> bool

module Dkey: sig
  val prepare: category
  val logic_normalizer: category
  val bound_variables: category
  val interval: category
  val mtracking: category
  val typing: category
  val labels: category
  val translation: category
end

val setup: ?rtl:bool -> unit -> unit
(** Verify and initialize the options of the current project according to the
    options set by the user.
    If [rtl] is true, then the project being modified is the RTL project. *)

(*
Local Variables:
compile-command: "make -C ../../../.."
End:
*)
