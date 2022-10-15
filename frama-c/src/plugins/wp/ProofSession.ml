(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

open Wpo

type script =
  | NoScript
  | Script of string
  | Deprecated of string

let files : (string,script) Hashtbl.t = Hashtbl.create 32

let jsonfile (dir:Datatype.Filepath.t) =
  Format.sprintf "%s/%s.json" (dir :> string)

let get_script_dir ~force =
  Wp_parameters.get_session_dir ~force "script"

let filename ~force wpo =
  let dscript = get_script_dir ~force in
  jsonfile dscript wpo.po_sid (* no model in name *)

let legacies wpo =
  let mid = WpContext.MODEL.id wpo.po_model in
  let dscript = Wp_parameters.get_session_dir ~force:false "script" in
  let dmodel = Wp_parameters.get_session_dir ~force:false mid in
  [
    jsonfile dscript wpo.po_gid ;
    jsonfile dmodel wpo.po_gid ;
  ]

let get wpo =
  let f = filename ~force:false wpo in
  try Hashtbl.find files f
  with Not_found ->
    let script =
      if Sys.file_exists f then Script f else
        try
          let f' = List.find Sys.file_exists (legacies wpo) in
          Wp_parameters.warning ~current:false
            "Deprecated script for '%s'" wpo.po_sid ;
          Deprecated f'
        with Not_found -> NoScript
    in Hashtbl.add files f script ; script

let pp_file fmt s = Filepath.Normalized.(pretty fmt (of_string s))

let pp_script_for fmt wpo =
  match get wpo with
  | Script f -> Format.fprintf fmt "script '%a'" pp_file f
  | Deprecated f -> Format.fprintf fmt "(deprecated) script '%a'" pp_file f
  | _ -> Format.fprintf fmt "script '%a'" pp_file @@ filename ~force:false wpo

let exists wpo =
  match get wpo with NoScript -> false | Script _ | Deprecated _ -> true

let load wpo =
  match get wpo with
  | NoScript -> `Null
  | Script f | Deprecated f ->
    if Sys.file_exists f then Json.load_file f else `Null

let remove wpo =
  match get wpo with
  | NoScript -> ()
  | Script f ->
    begin
      Extlib.safe_remove f ;
      Hashtbl.replace files f NoScript ;
    end
  | Deprecated f0 ->
    begin
      Wp_parameters.feedback
        "Removed deprecated script for '%s'" wpo.po_sid ;
      Extlib.safe_remove f0 ;
      let f = filename ~force:false wpo in
      Hashtbl.replace files f NoScript ;
    end

let save ~stdout wpo js =
  let empty =
    match js with
    | `Null | `List [] | `Assoc [] -> true
    | _ -> false in
  if stdout then
    Wp_parameters.result "Proof script for %s:@.%a"
      wpo.po_gid (Json.save_formatter ~pretty:true) js
  else
  if empty then remove wpo else
    match get wpo with
    | Script f ->
      Json.save_file f js
    | NoScript ->
      begin
        let f = filename ~force:true wpo in
        Json.save_file f js ;
        Hashtbl.replace files f (Script f) ;
      end
    | Deprecated f0 ->
      begin
        Wp_parameters.feedback
          "Upgraded script for '%s'" wpo.po_sid ;
        Extlib.safe_remove f0 ;
        let f = filename ~force:true wpo in
        Json.save_file f js ;
        Hashtbl.replace files f (Script f) ;
      end

let get_marks_dir ~force =
  let scripts = Wp_parameters.get_session_dir ~force "script" in
  let path = Datatype.Filepath.concat scripts ".marks" in
  if force then Wp_parameters.make_output_dir (path :> string) ;
  path

let remove_marks ~dry =
  let marks = get_marks_dir ~force:false in
  let as_str = (marks :> string) in
  if Sys.file_exists as_str && Sys.is_directory as_str then
    if dry
    then Wp_parameters.feedback "[dry] remove marks"
    else Extlib.safe_remove_dir as_str

let reset_marks () =
  remove_marks ~dry:false ;
  ignore @@ get_marks_dir ~force:true

let mark goal =
  let marks = get_marks_dir ~force:false in
  let as_str = (marks :> string) in
  if Sys.file_exists as_str && Sys.is_directory as_str then
    let mark = Datatype.Filepath.concat marks (goal.po_sid ^ ".json") in
    if Sys.file_exists (mark :> string) then ()
    else close_out @@ open_out (mark :> string)

module StringSet = Datatype.String.Set

let remove_unmarked_files ~dry =
  let dir = (get_script_dir ~force:false :> string) in
  if Sys.file_exists dir && Sys.is_directory dir then
    let marks = (get_marks_dir ~force:false :> string) in
    if Sys.file_exists marks && Sys.is_directory marks then
      begin
        let files =
          Array.fold_left
            (fun s f -> StringSet.add f s) StringSet.empty (Sys.readdir dir)
        in
        let marks =
          Array.fold_left
            (fun s f -> StringSet.add f s) StringSet.empty (Sys.readdir marks)
        in
        let orphans = StringSet.diff files marks in
        let orphans = StringSet.remove ".marks" orphans in
        let remove file =
          let path = dir ^ "/" ^ file in
          if dry
          then Wp_parameters.feedback "[dry] rm %s" path
          else Sys.remove path
        in
        StringSet.iter remove orphans ;
        remove_marks ~dry
      end
