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

open Cil_datatype
open Cil_types

open Misc

module AI = Abstract_interp

module Options = Reduc_options

let not_yet ~what =
  Options.warning "Not yet: %s" what

(* [int_to_predicate ~loc lop te i] create a predicate where [te] [lop] [i]. *)
let int_to_predicate ~loc ~lop te (i: Integer.t) =
  let ti = Logic_const.tint i in
  Logic_const.prel ~loc (lop, te, ti)

(* [float_to_predicate ~loc lop te f] create a predicate where [te] [lop] [f]. *)
let float_to_predicate ~loc ~lop t f =
  let tf = Logic_const.treal ~loc f in
  Logic_const.prel ~loc (lop, t, tf)

(* [interval_to_predicate_opt ~loc te min max] may create an interval
   predicate where [min] <= [te] <= [max]. *)
let interval_to_predicate_opt ~loc te min max =
  let min_predicate =
    int_to_predicate ~loc ~lop:Rge te
  and max_predicate =
    int_to_predicate ~loc ~lop:Rle te
  in
  Extlib.merge_opt
    (fun _ pmin pmax -> Logic_const.pand ~loc (pmin, pmax))
    ()
    (Option.map min_predicate min)
    (Option.map max_predicate max)

(* [congruence_to_predicate_opt ~loc te rem modulo] may create a congruence
   predicate where [te] mod [modulo] equals [rem] *)
let congruence_to_predicate_opt ~loc te rem modulo =
  if Integer.(equal modulo one) then None
  else
    let tmodulo = Logic_const.tint ~loc modulo in
    let tbinop = TBinOp(Mod, te, tmodulo) in
    (* since 0 <= rem < mod *)
    let tmodop = Logic_const.term ~loc tbinop (Linteger) in
    let p = int_to_predicate ~loc ~lop:Req tmodop rem in
    Some p

let fval_to_predicate ~loc t f =
  match Ival.min_and_max_float f with
  | None, false -> assert false
  | _, true -> Logic_const.pfalse (* todo *)
  | Some (fmn, fmx), _ ->
    let mn = Fval.F.to_float fmn in
    let mx = Fval.F.to_float fmx in
    let pmn = float_to_predicate ~loc ~lop:Rge t mn in
    let pmx = float_to_predicate ~loc ~lop:Rle t mx in
    Logic_const.pand ~loc (pmn, pmx)

(* [ival_to_predicate_opt ~loc t ival] may create a predicate from different
   domains contained in [ival]. *)
let ival_to_predicate_opt ~loc t ival =
  if Ival.is_float ival
  then Some (fval_to_predicate ~loc t ival)
  else
    match Ival.project_small_set ival with
    | Some is ->
      let ps = List.map (int_to_predicate ~loc ~lop:Req t) is in
      let pors = Logic_const.pors ps in
      Some pors
    | None ->
      match Ival.min_max_r_mod ival with
      | (None, None, _, modulo) when AI.Int.is_one modulo ->(*Top*) None
      | (min, max, rem, modulo) ->
        let pint = interval_to_predicate_opt ~loc t min max in
        let pcon = congruence_to_predicate_opt ~loc t rem modulo in
        Extlib.merge_opt
          (fun _ pint pcon -> Logic_const.pand ~loc (pint, pcon))
          ()
          pint
          pcon


(* [valid_to_predicate_opt ~loc t valid] may create validity predicate *only*
   for valid locations. *)
let valid_to_predicate_opt ~loc t valid =
  let here_lbl = BuiltinLabel Here in
  match valid with
  | Base.Empty -> None
  | Base.Known (bmn, bmx) | Base.Unknown (bmn, Some bmx, _) ->
    let tbmn = Cil.lconstant ~loc bmn in
    let tbmx = Cil.lconstant ~loc bmx in
    let p = Logic_const.pvalid_range ~loc (here_lbl, t, tbmn, tbmx) in
    Some p
  | Base.Unknown (_, _, _) -> None
  | Base.Variable { Base.min_alloc = bmn } when Integer.(equal bmn minus_one) ->
    not_yet ~what:"Invalid Base.Variable above max_alloc";
    None
  | Base.Variable { Base.min_alloc = bmn; Base.max_alloc = bmx } ->
    not_yet ~what:"Invalid Base.Variable above max_alloc";
    let tbmn = Cil.lconstant ~loc bmn in
    let tbmx = Cil.lconstant ~loc bmx in
    let p = Logic_const.pvalid_range ~loc (here_lbl, t, tbmn, tbmx) in
    Some p
  | Base.Invalid ->
    not_yet ~what:"Invalid Base";
    None

let base_to_predicate ~loc t (b: Base.t) =
  match b with
  | Base.Var (_vi, valid) | Base.Allocated (_vi, _, valid) ->
    valid_to_predicate_opt ~loc t valid
  | Base.CLogic_Var (_lvi, _typ, _) -> raise (Not_implemented "Base.CLogic_Var")
  | Base.Null -> assert false (*by projecting ival*)
  | Base.String _ -> raise (Not_implemented "Base.String")


let base_offset_to_predicate ~loc t b o =
  if Ival.equal Ival.zero o then
    base_to_predicate ~loc t b
  else begin
    not_yet ~what:"Base w/ offsets";
    None
  end

let _base_offsets_to_predicate ~loc t (m: Cvalue.V.M.t) =
  let aux b o (acc: predicate list) =
    let p_opt = base_offset_to_predicate ~loc t b o in
    (Option.to_list p_opt) @ acc
  in
  match Cvalue.V.M.fold aux m [] with
  | [] -> None
  | ps -> Some (Logic_const.pands ps)

let value_to_predicate_opt ?(loc=Location.unknown) t v =
  let open Cvalue.V in
  match v with
  | Top _ -> None
  | Map _m ->
    try
      let ival = project_ival v in
      ival_to_predicate_opt ~loc t ival
    with
    | Not_based_on_null -> (* base_offsets_to_predicate ~loc t m *) None

let exp_to_predicate ?(loc=Location.unknown) stmt e =
  let value = Eva.Results.(before stmt |> eval_exp e |> as_ival) in
  let te = Logic_utils.expr_to_term ~coerce:false e in
  Option.bind (Result.to_option value) (ival_to_predicate_opt ~loc te)

let lval_to_predicate ?(loc=Location.unknown) stmt lv =
  let value = Eva.Results.(before stmt |> eval_lval lv |> as_ival) in
  let e = Cil.new_exp ~loc (Lval lv) in
  let te = Logic_utils.expr_to_term ~coerce:false e in
  Option.bind (Result.to_option value) (ival_to_predicate_opt ~loc te)
