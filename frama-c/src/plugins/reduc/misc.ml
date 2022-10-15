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

module Options = Reduc_options


exception Not_implemented of string

let not_implemented ~what =
  Options.warning "Not implemented: `%s'. Ignoring." what


let emitter =
  Emitter.create
    "Reduc"
    [ Emitter.Code_annot; Emitter.Property_status ]
    ~correctness:[]
    ~tuning:[]

(* ******************************************************)
(*      Annotations and function contracts helpers      *)
(* ******************************************************)
let validate_ip ip =
  Property_status.emit emitter ~hyps:[] ip Property_status.True

let assert_and_validate ~kf stmt p =
  let p =  { tp_kind = Assert ; tp_statement = p } in
  let annot = Logic_const.new_code_annotation (AAssert([], p)) in
  Annotations.add_code_annot emitter ~kf stmt annot ;
  List.iter
    validate_ip
    (Property.ip_of_code_annot kf stmt annot)
