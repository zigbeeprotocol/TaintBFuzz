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

(* -------------------------------------------------------------------------- *)
(* --- Server Plugin & Options                                            --- *)
(* -------------------------------------------------------------------------- *)

module P = Plugin.Register
    (struct
      let name = "Server"
      let shortname = "server"
      let help = "Frama-C Request Server (experimental)"
    end)

include P

(* -------------------------------------------------------------------------- *)
(* --- Server General Options                                             --- *)
(* -------------------------------------------------------------------------- *)

module Polling = P.Int
    (struct
      let option_name = "-server-polling"
      let arg_name = "ms"
      let default = 50
      let help = "Server polling time period, in milliseconds (default 50ms)"
    end)

module AutoLog = P.False
    (struct
      let option_name = "-server-auto-log"
      let help =
        "Start monitoring logs before server is running (default is false)"
    end)

(* -------------------------------------------------------------------------- *)
(* --- Doc Options                                                        --- *)
(* -------------------------------------------------------------------------- *)

let server_doc = add_group "Server Doc Generation"
let () = Parameter_customize.set_group server_doc
let () = Parameter_customize.do_not_save ()

module Doc = P.Filepath
    (struct
      let option_name = "-server-doc"
      let arg_name = "dir"
      let file_kind = "Directory"
      let existence = Fc_Filepath.Must_exist
      let help = "Output a markdown documentation of the server in <dir>"
    end)

let wpage = register_warn_category "inconsistent-page"
let wkind = register_warn_category "inconsistent-kind"
let wname = register_warn_category "invalid-name"

(* -------------------------------------------------------------------------- *)
(* --- Filepath Normalization                                             --- *)
(* -------------------------------------------------------------------------- *)

let use_relative_filepath = register_category "use-relative-filepath"
let has_relative_filepath () = is_debug_key_enabled use_relative_filepath

(* -------------------------------------------------------------------------- *)
