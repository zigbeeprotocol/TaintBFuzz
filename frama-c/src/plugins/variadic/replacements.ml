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

(* State to store the association between a replaced function and the original
   function. *)
module Replacements =
  Cil_state_builder.Varinfo_hashtbl
    (Cil_datatype.Varinfo)
    (struct
      let size = 17
      let name = "replacements"
      let dependencies = [ Options.Enabled.self; Options.Strict.self ]
    end)

let add new_vi old_vi =
  Replacements.add new_vi old_vi

let find new_vi =
  Replacements.find new_vi

let mem new_vi =
  Replacements.mem new_vi
