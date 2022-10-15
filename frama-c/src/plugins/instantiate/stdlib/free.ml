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

let unexpected = Options.fatal "Stdlib.Free: unexpected: %s"

let function_name = "free"

let null_pointer ?loc ptr =
  prel ?loc (Req, ptr, term ?loc Tnull ptr.term_type)

let not_null_pointer ?loc ptr =
  prel ?loc (Rneq, ptr, term ?loc Tnull ptr.term_type)

let generate_requires loc ptr =
  let null_pointer = null_pointer ~loc ptr in
  let freeable = pfreeable ~loc (here_label, ptr) in
  let p = por ~loc (null_pointer, freeable) in
  [ new_predicate { p with pred_name = ["freeable"] } ]

let generate_global_assigns ptr =
  let assigns_heap = assigns_heap [ ptr ] in
  Writes [ assigns_heap ]

let make_behavior_deallocation loc ptr =
  let assumes = [ new_predicate (not_null_pointer ~loc ptr) ] in
  let assigns = generate_global_assigns ptr in
  let alloc   = FreeAlloc ([new_identified_term ptr], []) in
  let freed =
    { (pallocable ~loc (here_label, ptr)) with pred_name = ["freed"] }
  in
  let ensures = [ Normal, new_predicate freed ] in
  make_behavior ~name:"allocation" ~assumes ~assigns ~alloc ~ensures ()

let make_behavior_no_deallocation loc ptr =
  let assumes = [ new_predicate (null_pointer ~loc ptr) ] in
  let assigns = Writes [] in
  let ensures = [ ] in
  let alloc = allocates_nothing () in
  make_behavior ~name:"no_allocation" ~assumes ~assigns ~ensures ~alloc ()

let generate_spec _typ loc { svar = vi } =
  let ptr = match Cil.getFormalsDecl vi with
    | [ ptr ] -> cvar_to_tvar ptr
    | _ -> unexpected "ill-formed fundec in specification generation"
  in
  let requires = generate_requires loc ptr in
  let assigns = generate_global_assigns ptr in
  let alloc   = FreeAlloc ([new_identified_term ptr], []) in
  make_funspec [
    make_behavior ~requires ~assigns ~alloc () ;
    make_behavior_deallocation loc ptr ;
    make_behavior_no_deallocation loc ptr
  ] ()

let generate_prototype alloc_t =
  let name = function_name ^ "_" ^ (string_of_typ alloc_t) in
  let params = [
    ("ptr", (ptr_of alloc_t), [])
  ] in
  name, (TFun(Cil.voidType, Some params, false, []))

let well_typed_call _ret _fct args =
  match args with
  | [ ptr ] ->
    let t = Cil.typeOf (Cil.stripCasts ptr) in
    Cil.isPointerType t && not (Cil.isVoidPtrType t)
  | _ -> false

let key_from_call _ret _fct args =
  match args with
  | [ ptr ] ->
    let ptr = Cil.stripCasts ptr in
    let ptr_t = Cil.unrollTypeDeep (Cil.typeOf ptr) in
    let ptr_t = Cil.type_remove_qualifier_attributes_deep ptr_t in
    Cil.typeOf_pointed ptr_t
  | _ -> unexpected "trying to generate a key on an ill-typed call"

let retype_args _typ args = List.map Cil.stripCasts args
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
