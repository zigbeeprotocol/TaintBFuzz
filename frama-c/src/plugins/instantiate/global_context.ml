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

module Table = Datatype.String.Hashtbl

let varinfos = Table.create 13
let logic_functions = Table.create 13
let axiomatics = Table.create 13

let get_variable name make =
  if Table.mem varinfos name then Table.find varinfos name
  else begin
    try Globals.Vars.find_from_astinfo name VGlobal
    with Not_found ->
      let vi = make () in
      Table.add varinfos name vi ;
      vi
  end

let get_logic_function name make =
  if Table.mem logic_functions name then Table.find logic_functions name
  else begin
    match Logic_env.find_all_logic_functions name with
    | [] ->
      let li = make () in
      Table.add logic_functions name li ;
      Logic_utils.add_logic_function li ;
      li
    | [x] -> x
    | _ :: _ -> Options.not_yet_implemented "Logic function overloading"
  end

let in_axiomatic_functions = Table.create 13

let get_logic_function_in_axiomatic name make =
  if Table.mem in_axiomatic_functions name then
    Table.find in_axiomatic_functions name
  else begin
    let make_then_find name =
      let open Cil_types in
      let (ax_name, ax_list), functions = make () in
      List.iter
        (fun f ->
           Table.add in_axiomatic_functions f.l_var_info.lv_name f ;
           Logic_utils.add_logic_function f)
        functions ;
      Table.add axiomatics ax_name ax_list ;
      Table.find in_axiomatic_functions name
    in
    try match Logic_env.find_all_logic_functions name with
      | [] -> make_then_find name
      | [x] -> x
      | _ :: _ -> Options.not_yet_implemented "Logic function overloading"
    with Not_found ->
      Options.fatal "Failed to build %s" name
  end

let clear () = Table.clear varinfos

let globals loc =
  let open Cil_types in
  let l = [] in
  let l =
    Table.fold (fun _ x l -> GVarDecl(x, loc) :: l) varinfos l
  in
  let annot x loc = GAnnot(x, loc) in
  let fun_or_pred x loc = annot (Dfun_or_pred (x, loc)) loc in
  let axiomatic name list loc = annot(Daxiomatic(name, list, [], loc)) loc in
  let l = Table.fold (fun _ x l -> fun_or_pred x loc :: l) logic_functions l in
  let l = Table.fold (fun n x l -> axiomatic n x loc :: l) axiomatics l in
  l
