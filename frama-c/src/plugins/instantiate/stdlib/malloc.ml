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

let function_name = "malloc"

let unexpected = Options.fatal "Stdlib.Malloc: unexpected: %s"

let generate_global_assigns loc ptr_type size =
  let assigns_result = assigns_result ~loc ptr_type [ size ] in
  let assigns_heap = assigns_heap [ size ] in
  Writes [ assigns_result ; assigns_heap ]

let make_behavior_allocation loc ptr_type size =
  let assumes = [ is_allocable ~loc size ] in
  let assigns = generate_global_assigns loc ptr_type size in
  let alloc   = allocates_result ~loc ptr_type in
  let ensures = [ Normal, fresh_result ~loc ptr_type size ] in
  make_behavior ~name:"allocation" ~assumes ~assigns ~alloc ~ensures ()

let make_behavior_no_allocation loc ptr_type size =
  let assumes = [ isnt_allocable ~loc size ] in
  let assigns = Writes [assigns_result ~loc ptr_type []] in
  let ensures = [ Normal, null_result ~loc ptr_type ] in
  let alloc = allocates_nothing () in
  make_behavior ~name:"no_allocation" ~assumes ~assigns ~ensures ~alloc ()

let generate_spec alloc_typ loc { svar = vi } =
  let (csize) = match Cil.getFormalsDecl vi with
    | [ size ] -> size
    | _ -> unexpected "ill-formed fundec in specification generation"
  in
  let size = tlogic_coerce ~loc (cvar_to_tvar csize) Linteger in
  let requires = [ valid_size ~loc alloc_typ size ] in
  let assigns = generate_global_assigns loc (ptr_of alloc_typ) size in
  let alloc = allocates_result ~loc (ptr_of alloc_typ) in
  make_funspec [
    make_behavior ~requires ~assigns ~alloc () ;
    make_behavior_allocation loc (ptr_of alloc_typ) size ;
    make_behavior_no_allocation loc (ptr_of alloc_typ) size
  ] ()

let generate_prototype alloc_t =
  let name = function_name ^ "_" ^ (string_of_typ alloc_t) in
  let params = [
    ("size", size_t (), [])
  ] in
  name, (TFun((ptr_of alloc_t), Some params, false, []))

let well_typed_call ret _fct args =
  match ret, args with
  | Some ret, [ _ ] ->
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
