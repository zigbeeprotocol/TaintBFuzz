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

include Plugin.Register
    (struct
      let name = "dive"
      let shortname = "dive"
      let help = "An interactive imprecision graph generator for Eva."
    end)

module OutputDot = Filepath
    (struct
      let option_name = "-dive-output-dot"
      let arg_name = "output.dot"
      let file_kind = "DOT"
      let existence = Fc_Filepath.Indifferent
      let help = "Outputs the built graph in DOT format to the specified file."
    end)

module OutputJson = Filepath
    (struct
      let option_name = "-dive-output-json"
      let arg_name = "output.json"
      let file_kind = "JSON"
      let existence = Fc_Filepath.Indifferent
      let help = "Outputs the built graph in JSON format to the specified."
    end)

module DepthLimit = Int
    (struct
      let option_name = "-dive-depth-limit"
      let help = "Build dependencies up to a depth of N."
      let arg_name = "N"
      let default = 3
    end)

module FromFunctionAlarms = Kernel_function_set
    (struct
      let option_name = "-dive-from-alarms"
      let help = "Build the graph from the alarms emitted in the given functions."
      let arg_name = "f1,..."
    end)

module Varinfo =
struct
  include Cil_datatype.Varinfo

  let of_string s =
    let regexp = Str.regexp "^\\([_a-zA-Z0-9]+\\)::\\([_a-zA-Z0-9]+\\)$" in
    if Str.string_match regexp s 0 then
      let function_name = Str.matched_group 1 s
      and variable_name = Str.matched_group 2 s in
      let kf = try Globals.Functions.find_by_name function_name
        with Not_found ->
          raise (Cannot_build ("no function '" ^ function_name ^ "'"))
      in
      try Globals.Vars.find_from_astinfo variable_name (VLocal kf)
      with Not_found ->
      try Globals.Vars.find_from_astinfo variable_name (VFormal kf)
      with Not_found ->
        raise (Cannot_build ("no variable '" ^ variable_name ^ "' in function "
                             ^ function_name))
    else
      let regexp = Str.regexp "^[_a-zA-Z0-9]+$" in
      if not (Str.string_match regexp s 0) then
        raise (Cannot_build ("wrong syntax: '" ^ s ^ "'"));
      match Globals.Syntactic_search.find_in_scope s Cil_types.Program with
      | Some vi -> vi
      | None ->
        raise (Cannot_build ("no global variable '" ^ s ^ "'"))

  let to_string vi =
    match Kernel_function.find_defining_kf vi with
    | None -> vi.vname
    | Some kf -> Kernel_function.get_name kf ^ "::" ^ vi.vname

  let of_singleton_string = no_element_of_string
end

module type Varinfo_set = Parameter_sig.Set
  with type elt = Cil_types.varinfo
   and type t = Cil_datatype.Varinfo.Set.t

module Varinfo_set (X: Parameter_sig.Input_with_arg) =
  Make_set
    (Varinfo)
    (struct
      include X
      let dependencies = []
      let default = Cil_datatype.Varinfo.Set.empty
    end)

module FromBases = Varinfo_set
    (struct
      let option_name = "-dive-from-variables"
      let help = "Build the graph from these local variables."
      let arg_name = "f::v,..."
    end)

module UnfoldedBases = Varinfo_set
    (struct
      let option_name = "-dive-unfold"
      let help = "Defines the composite variables which should be \
                  unfolded into individual cells."
      let arg_name = "f::v,..."
    end)

module HiddenBases = Varinfo_set
    (struct
      let option_name = "-dive-hide"
      let help = "Defines the variables which must not be \
                  displayed in the graph. The dependencies for these bases \
                  are not computed either."
      let arg_name = "f::v,..."
    end)
