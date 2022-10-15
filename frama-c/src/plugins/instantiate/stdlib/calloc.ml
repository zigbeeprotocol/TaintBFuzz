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

open Basic_blocks
open Basic_alloc
open Cil_types
open Logic_const

let function_name = "calloc"

let unexpected = Options.fatal "Stdlib.Calloc: unexpected: %s"

let pset_len_to_zero ?loc alloc_type num size =
  let eq_simpl_value ?loc t =
    let value = match Logic_utils.unroll_type t.term_type with
      | Ctype(TPtr(_)) -> term Tnull t.term_type
      | Ctype(TFloat(_)) -> treal ?loc 0.
      | Ctype(TInt(_) | TEnum (_)) -> tinteger ?loc 0
      | _ -> unexpected "non atomic type during equality generation"
    in
    prel ?loc (Req, t, value)
  in
  let ptr_type = ptr_of alloc_type in
  let result = tresult ?loc ptr_type in
  let p = if Cil.has_flexible_array_member alloc_type then
      let access = Cil.mkTermMem ~addr:result ~off:TNoOffset in
      let access = term ?loc (TLval access) (Ctype alloc_type) in
      (* Note: calloc with flexible array member assumes num == 1 *)
      punfold_flexible_struct_pred ?loc access size eq_simpl_value

    else
      punfold_all_elems_pred ?loc result num eq_simpl_value
  in
  new_predicate { p with pred_name = [ "zero_initialization" ] }

let generate_requires ?loc alloc_type num size =
  let only_one = if Cil.has_flexible_array_member alloc_type then
      let p = prel ?loc (Req, num, Cil.lone ?loc ()) in
      Some (new_predicate { p with pred_name = ["only_one"] })
    else
      None
  in
  [ valid_size ?loc alloc_type size ] @ (Option.to_list only_one)

let pinitialized_len ?loc alloc_type num size =
  let result = tresult ?loc (ptr_of alloc_type) in
  let initialized ?loc t =
    let t = match t.term_node, Logic_utils.unroll_type t.term_type with
      | TLval (lv), (Ctype _ as t) ->
        Logic_utils.mk_logic_AddrOf ?loc lv t
      | _ -> unexpected "non lvalue or non c-type during initialized generation"
    in
    pinitialized ?loc (here_label, t)
  in
  let p = if Cil.has_flexible_array_member alloc_type then
      let access = Cil.mkTermMem ~addr:result ~off:TNoOffset in
      let access = term ?loc (TLval access) (Ctype alloc_type) in
      (* Note: calloc with flexible array member assumes num == 1 *)
      punfold_flexible_struct_pred ?loc access size initialized
    else
      punfold_all_elems_pred ?loc result num initialized
  in
  new_predicate { p with pred_name = [ "initialization" ] }

let generate_global_assigns loc alloc_type num size =
  let assigns_result = assigns_result ~loc (ptr_of alloc_type) [ num ; size ] in
  let assigns_heap = assigns_heap [ num ; size ] in
  Writes [ assigns_result ; assigns_heap ]

let make_behavior_allocation loc alloc_type num size =
  let ptr_type = ptr_of alloc_type in
  let len = term ~loc (TBinOp(Mult, num, size)) Linteger in
  let assumes = [ is_allocable ~loc len ] in
  let assigns = generate_global_assigns loc alloc_type num size in
  let alloc   = allocates_result ~loc ptr_type in
  let ensures = [
    Normal, fresh_result ~loc ptr_type len ;
    Normal, pset_len_to_zero ~loc alloc_type num size ;
    Normal, pinitialized_len ~loc alloc_type num size
  ] in
  make_behavior ~name:"allocation" ~assumes ~assigns ~alloc ~ensures ()

let make_behavior_no_allocation loc alloc_type num size =
  let len = term ~loc (TBinOp(Mult, num, size)) Linteger in
  let ptr_type = ptr_of alloc_type in
  let assumes = [ isnt_allocable ~loc len ] in
  let assigns = Writes [assigns_result ~loc ptr_type []] in
  let ensures = [ Normal, null_result ~loc ptr_type ] in
  let alloc = allocates_nothing () in
  make_behavior ~name:"no_allocation" ~assumes ~assigns ~ensures ~alloc ()

let generate_spec alloc_type loc { svar = vi } =
  let (cnum, csize) = match Cil.getFormalsDecl vi with
    | [ cnum ; csize ] -> cnum, csize
    | _ -> unexpected "ill-formed fundec in specification generation"
  in
  let num = tlogic_coerce ~loc (cvar_to_tvar cnum) Linteger in
  let size = tlogic_coerce ~loc (cvar_to_tvar csize) Linteger in
  let requires = generate_requires ~loc alloc_type num size in
  let assigns = generate_global_assigns loc alloc_type num size in
  let alloc = allocates_result ~loc (ptr_of alloc_type) in
  make_funspec [
    make_behavior ~requires ~assigns ~alloc () ;
    make_behavior_allocation loc alloc_type num size ;
    make_behavior_no_allocation loc alloc_type num size
  ] ()

let generate_prototype alloc_type =
  let name = function_name ^ "_" ^ (string_of_typ alloc_type) in
  let params = [
    ("num", size_t (), []) ;
    ("size", size_t (), [])
  ] in
  name, (TFun((ptr_of alloc_type), Some params, false, []))

let well_typed_call ret _fct args =
  match ret, args with
  | Some ret, [ _ ; _ ] ->
    let t = Cil.typeOfLval ret in
    Cil.isPointerType t && not (Cil.isVoidPtrType t) &&
    Cil.isCompleteType (Cil.typeOf_pointed t)
  | _ -> false

let key_from_call ret _fct _ =
  match ret with
  | Some ret ->
    let ret_t = Cil.unrollTypeDeep (Cil.typeOfLval ret) in
    let ret_t = Cil.type_remove_qualifier_attributes_deep ret_t in
    Cil.typeOf_pointed ret_t
  | _ -> unexpected "trying to generate a key on an ill-typed call"

let retype_args _typ args = args
let args_for_original _typ args = args

let () = Transform.register (module struct
    module Hashtbl = Cil_datatype.Typ.Hashtbl
    type override_key = typ

    let function_name = function_name
    let well_typed_call = well_typed_call
    let key_from_call = key_from_call
    let retype_args = retype_args
    let generate_prototype = generate_prototype
    let generate_spec = generate_spec
    let args_for_original = args_for_original
  end)
