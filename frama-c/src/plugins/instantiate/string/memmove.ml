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
open Mem_utils

let function_name = "memmove"

let requires = memcpy_memmove_common_requires
let assigns = memcpy_memmove_common_assigns
let ensures = memcpy_memmove_common_ensures "moved"
let generate_spec = mem2s_spec ~requires ~assigns ~ensures

module Function =
struct
  let name = function_name
  let prototype () =
    Ptr,
    [
      ("dest", Ptr, Strip);
      ("src" , CPtr, Strip);
      ("len",  Data (Basic_blocks.size_t()), Id)
    ]
  let well_typed = Mem_utils.mem2s_typing
end
module Memmove_base = Mem_utils.Make(Function)

let () = Transform.register (module struct
    module Hashtbl = Cil_datatype.Typ.Hashtbl
    type override_key = typ

    let function_name = function_name
    let well_typed_call = Memmove_base.well_typed_call
    let key_from_call = Memmove_base.key_from_call
    let retype_args = Memmove_base.retype_args
    let generate_prototype = Memmove_base.generate_prototype
    let generate_spec = generate_spec
    let args_for_original _ = Extlib.id
  end)
