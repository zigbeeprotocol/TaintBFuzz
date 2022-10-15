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

include Plugin.Register
    (struct
      let name = "Reduction"
      let shortname = "reduc"
      let help = "Generate ACSL annotations from Eva information"
    end)

module Reduc =
  Bool
    (struct
      let option_name = "-reduc"
      let help = "Use reduc"
      let default = false
    end)

module GenAnnot =
  String
    (struct
      let option_name = "-reduc-gen-annot"
      let arg_name = "gen-annot-heuristic"
      let help = "Heuristic to generate annotations from Eva"
      let default = "inout"
    end)
let () = GenAnnot.set_possible_values ["inout"; "all"]
