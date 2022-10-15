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

(** Declarations that are useful for plugins written on top of the results
    of Value. *)

open Cil_types

(* TODO: These types are already defined in Value_util. *)
type call_site = kernel_function * kinstr
(** Value call-site.
    A callsite [(f,p)] represents a call at function [f] invoked
    {i from} program point [p].
*)

type callstack = call_site list
(** Value callstacks, as used e.g. in Db.Value hooks.

    The head call site [(f,p)] is the most recent one,
    where current function [f] has been called from program point [p].

    Therefore, the tail call site is expected to be [(main,Kglobal)]
    where [main] is the global entry point.

    Moreover, given two consecutive call-sites […(_,p);(g,_)…] in a callstack,
    program point [p] is then expected to live in function [g].
*)

module Callsite: Datatype.S_with_collections with type t = call_site
module Callstack: sig
  include Datatype.S_with_collections with type t = callstack
  val pretty_debug : Format.formatter -> t -> unit

  (** Print a hash of the callstack when '-kernel-msg-key callstack'
      is enabled (prints nothing otherwise). *)
  val pretty_hash : Format.formatter -> t -> unit

  (** Print a call stack without displaying call sites. *)
  val pretty_short : Format.formatter -> t -> unit
end

type 'a callback_result =
  | Normal of 'a
  | NormalStore of 'a * int
  | Reuse of int

type call_froms = (Function_Froms.froms * Locations.Zone.t) option
(** If not None, the froms of the function, and its sure outputs;
    i.e. the dependencies of the result, and the dependencies
    of each zone written to. *)

(** Dependencies for the evaluation of a term or a predicate: for each
    program point involved, sets of zones that must be read *)
type logic_dependencies = Locations.Zone.t Cil_datatype.Logic_label.Map.t

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
