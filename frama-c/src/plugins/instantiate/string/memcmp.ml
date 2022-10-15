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
open Logic_const
open Basic_blocks

let function_name = "memcmp"

let requires loc _ s1 s2 len =
  List.map new_predicate [
    { (pcorrect_len_bytes ~loc s1.term_type len)
      with pred_name = ["aligned_end"] } ;
    { (pvalid_read_len_bytes ~loc here_label s1 len)
      with pred_name = ["valid_read_s1"] } ;
    { (pvalid_read_len_bytes ~loc here_label s2 len)
      with pred_name = ["valid_read_s2"] } ;
  ]

let presult_memcmp ?loc p1 p2 len =
  let eq = punfold_all_elems_eq ?loc p1 p2 len in
  let res = prel ?loc (Req, (tresult ?loc Cil.intType), (tinteger ?loc 0)) in
  piff ?loc (res, eq)

let assigns loc _ s1 s2 len =
  let indirect_range loc s len =
    new_identified_term
      { (tunref_range_bytes_len ~loc s len) with term_name = ["indirect"] }
  in
  let s1_range = indirect_range loc s1 len in
  let s2_range = indirect_range loc s2 len in
  let result = new_identified_term (tresult Cil.intType) in
  let res = result, From [s1_range ; s2_range] in
  Writes [ res ]

let presult_memcmp_len_bytes ?loc p1 p2 bytes_len =
  plet_len_div_size ?loc p1.term_type bytes_len (presult_memcmp ?loc p1 p2)

let ensures loc _ s1 s2 len =
  List.map (fun p -> Normal, new_predicate p) [
    { (presult_memcmp_len_bytes ~loc s1 s2 len) with pred_name = [ "equals" ] }
  ]

let generate_spec = Mem_utils.mem2s_spec ~requires ~assigns ~ensures

module Function =
struct
  open Mem_utils
  let name = function_name
  let prototype () =
    Data Cil.intType,
    [
      ("s1" , CPtr,Strip) ;
      ("s2" , CPtr,Strip) ;
      ("len", Data (size_t ()) ,Id)
    ]
  let well_typed = Mem_utils.mem2s_typing
end
module Memcmp_base = Mem_utils.Make(Function)

let () = Transform.register (module struct
    module Hashtbl = Cil_datatype.Typ.Hashtbl
    type override_key = typ

    let function_name = function_name
    let well_typed_call = Memcmp_base.well_typed_call
    let key_from_call = Memcmp_base.key_from_call
    let retype_args = Memcmp_base.retype_args
    let generate_prototype = Memcmp_base.generate_prototype
    let generate_spec = generate_spec
    let args_for_original _ = Extlib.id
  end)
