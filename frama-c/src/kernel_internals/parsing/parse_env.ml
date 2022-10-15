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

(* maps filepaths to bools (true iff the file existed at the moment
   the reference was read *)
let referenced_files = Hashtbl.create 7

module SourceFiles =
  State_builder.Hashtbl(Datatype.Filepath.Hashtbl)(Datatype.String)
    (struct
      let name = "SourceFiles"
      let dependencies = [ Kernel.Files.self ]
      let size = 1
    end)

(* maps .i/.pp files to their workdir (when a JCDB is used) *)
module PreprocessingWorkdir =
  State_builder.Hashtbl(Datatype.Filepath.Hashtbl)(Datatype.String)
    (struct
      let name = "PreprocessingWorkdir"
      let dependencies =
        [ Kernel.Files.self; Kernel.JsonCompilationDatabase.self ]
      let size = 2
    end)

let set_workdir file workdir =
  PreprocessingWorkdir.replace file workdir

let get_workdir file =
  try
    Some (PreprocessingWorkdir.find file)
  with Not_found -> None

let store_referenced_source fname =
  let fp = Datatype.Filepath.of_string fname in
  if not (Hashtbl.mem referenced_files fp) then begin
    try
      let inchan = open_in_bin (fp :> string) in
      let contents = really_input_string inchan (in_channel_length inchan) in
      close_in inchan;
      SourceFiles.replace fp contents;
      Hashtbl.add referenced_files fp true
    with Sys_error s ->
      Kernel.warning ~once:true ~wkey:Kernel.wkey_file_not_found
        "Cannot find referenced file %S (%s), ignoring" fname s;
      Hashtbl.add referenced_files fp false
  end

let scan_source_for_references ~workdir contents =
  let re_hash =
    Str.regexp "^#[ \\t]*\\(line\\)?[ \\t]*[0-9]+[ \\t]+\"\\([^<>]*\\)\"[ \\t]+[0-9]*[ \\t]*$"
  in
  let lines = String.split_on_char '\n' contents in
  List.iter (fun line ->
      if Str.string_match re_hash line 0 then
        let file = Str.matched_group 2 line in
        let file =
          if String.contains file '"' then
            (* Special case: the filename contains double quotes;
               when this happens, the matched regex contains an extra backslash
               that must be removed. In other words, we must undo the quoting
               introduced by the C preprocessor. *)
            Str.global_replace (Str.regexp "\\\\\"") "\"" file
          else file
        in
        let file = if Filename.is_relative file && workdir <> None then
            (Option.get workdir) ^ "/" ^ file
          else file
        in
        store_referenced_source file
    ) lines

let open_source ~scan_references fname =
  let fp = Datatype.Filepath.of_string fname in
  try
    let s = SourceFiles.find fp in
    Ok s
  with Not_found ->
  try
    Kernel.feedback ~dkey:Kernel.dkey_file_source
      "opening source file: %S" fname;
    let inchan = open_in_bin (fp :> string) in
    let contents = really_input_string inchan (in_channel_length inchan) in
    close_in inchan;
    SourceFiles.replace fp contents;
    let workdir =
      try
        Some (PreprocessingWorkdir.find fp)
      with Not_found ->
        None
    in
    if scan_references then
      scan_source_for_references ~workdir contents;
    Ok contents
  with Sys_error s ->
    Error s
