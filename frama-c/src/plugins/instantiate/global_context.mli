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

(** The purpose of this module global definitions when it is needed by
    instantiation modules.
*)

(** [get_variable name f] searches for an existing variable [name]. If this
    variable does not exists, it is created using [f].

    The obtained varinfo does not need to be registered, nor [f] needs to
    perform the registration, it will be done by the transformation.
*)
val get_variable: string -> (unit -> varinfo) -> varinfo

(** [get_logic_function name f] searches for an existing logic function [name].
    If this function does not exists, it is created using [f]. If the logic
    function must be part of an axiomatic block **DO NOT** use this function,
    use [get_logic_function_in_axiomatic].

    Note that function overloading is not supported.
*)
val get_logic_function: string -> (unit -> logic_info) -> logic_info

(** [get_logic_function_in_axiomatic name f] searches for an existing logic
    function [name]. If this function does not exists, an axiomatic definition
    is created using [f].

    [f] must return:
    - the axiomatic in a form [name, list of the defintions (incl. functions)]
    - all functions that are part of the axiomatic definition

    Note that function overloading is not supported.
*)
val get_logic_function_in_axiomatic:
  string ->
  (unit -> (string * global_annotation list) * logic_info list) ->
  logic_info

(** Clears internal tables *)
val clear: unit -> unit

(** Creates a list of global for the elements that have been created *)
val globals: location -> global list
