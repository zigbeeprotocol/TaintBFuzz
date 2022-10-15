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

module Options = Reduc_options

let command_line () =
  let annoth = match Options.GenAnnot.get () with
    | "all" -> Collect.AnnotAll
    | "inout" -> Collect.AnnotInout
    | _ -> Options.fatal "Not a valid annotation heuristic"
  in
  annoth

let main () =
  if (Options.Reduc.get ()) then begin
    let annoth = command_line () in
    let env = Alarms.fold Collect.get_relevant (Collect.empty_env annoth) in
    Hyp.generate_hypotheses env;
    ()
  end

let () = Db.Main.extend main
