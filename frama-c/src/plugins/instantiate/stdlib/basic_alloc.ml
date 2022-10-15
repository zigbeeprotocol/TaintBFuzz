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

open Logic_const
open Basic_blocks
open Cil_types
open Extlib

let unexpected = Options.fatal "Stdlib.Basic_alloc: unexpected: %s"

let valid_size ?loc typ size =
  let p = match typ with
    | TComp (ci, _) when Cil.has_flexible_array_member typ ->
      let elem = match (last (Option.value ~default:[] ci.cfields)).ftype with
        | TArray(t, _, _) -> tinteger ?loc (Cil.bytesSizeOf t)
        | _ -> unexpected "non array last field on flexible structure"
      in
      let base = tinteger ?loc (Cil.bytesSizeOf typ) in
      let flex = tminus ?loc size base in
      let flex_mod = term ?loc (TBinOp(Mod, flex, elem)) Linteger in
      let flex_at_least_zero = prel ?loc (Rle, Cil.lzero (), flex) in
      let aligned_flex = prel ?loc (Req, Cil.lzero (), flex_mod) in
      pand ?loc (flex_at_least_zero, aligned_flex)
    | _ ->
      let elem = tinteger ?loc (Cil.bytesSizeOf typ) in
      let modulo = term ?loc (TBinOp(Mod, size, elem)) Linteger in
      prel(Req, Cil.lzero (), modulo)
  in
  new_predicate { p with pred_name = ["correct_size"] }

let heap_status () =
  let name = "__fc_heap_status" in
  let make () =
    let vi = Cil.makeVarinfo ~ghost:true true false name Cil.intType in
    vi.vstorage <- Extern ;
    vi
  in
  let vi = Global_context.get_variable name make in
  Basic_blocks.cvar_to_tvar vi

let make_is_allocable () =
  let name = "is_allocable" in
  {
    l_var_info = Cil_const.make_logic_var_global name (Ctype Cil.voidType) ;
    l_type = None ;
    l_tparams = [];
    l_labels = [FormalLabel("L")];
    l_profile = [Cil_const.make_logic_var_formal "i" Linteger] ;
    l_body = LBreads [new_identified_term (heap_status())];
  }

let make_axiomatic_is_allocable loc () =
  let is_allocable = make_is_allocable () in
  let lv_i = Cil_const.make_logic_var_quant "i" Linteger in
  let t_i = tvar lv_i in
  let zero = tinteger 0 in
  let max_value = Cil.max_unsigned_number (Cil.bitsSizeOf (size_t ())) in
  let max = term ~loc (TConst (Integer (max_value, None))) Linteger in
  let label = FormalLabel("L") in
  let cond = pand (prel (Rlt, t_i, zero), prel (Rgt, t_i, max)) in
  let app = pnot (papp (is_allocable,[label],[t_i])) in
  let prop = pforall ([lv_i], pimplies (cond, app)) in
  let prop = Logic_const.toplevel_predicate ~kind:Admit prop in
  let gfun = Dfun_or_pred(is_allocable, loc) in
  let axiom = Dlemma("never_allocable", [label],[],prop,[], loc) in
  ("dynamic_allocation", [gfun ; axiom]), [is_allocable]

let get_is_allocable loc =
  Global_context.get_logic_function_in_axiomatic
    "is_allocable" (make_axiomatic_is_allocable loc)

let pis_allocable ?loc size =
  let loc = match loc with
    | None -> Cil_datatype.Location.unknown
    | Some l -> l
  in
  let is_allocable = get_is_allocable loc in
  papp ~loc (is_allocable, [here_label], [size])

let is_allocable ?loc size =
  let p = pis_allocable ?loc size in
  new_predicate { p with pred_name = [ "allocable" ]}

let isnt_allocable ?loc size =
  let p = pnot ?loc (pis_allocable ?loc size) in
  new_predicate { p with pred_name = [ "allocable" ]}

let assigns_result ?loc typ deps =
  let heap_status = new_identified_term (heap_status ()) in
  let deps = match deps with
    | [] -> []
    | l -> heap_status :: (List.map new_identified_term l)
  in
  let result = new_identified_term (tresult ?loc typ) in
  result, From deps

let assigns_heap deps =
  let heap_status = new_identified_term (heap_status ()) in
  let deps = List.map new_identified_term deps in
  heap_status, From (heap_status :: deps)

let allocates_nothing () =
  FreeAlloc([],[])

let allocates_result ?loc t =
  FreeAlloc ([], [new_identified_term (tresult ?loc t)])

let fresh_result ?loc typ size =
  let result = tresult ?loc typ in
  let p = pfresh ?loc (old_label, here_label, result, size) in
  new_predicate { p with pred_name = [ "fresh_result" ] }

let null_result ?loc typ =
  let tresult = tresult ?loc typ in
  let tnull = term ?loc Tnull (Ctype typ) in
  let p = prel ?loc (Req, tresult, tnull) in
  new_predicate { p with pred_name = [ "null_result" ] }
