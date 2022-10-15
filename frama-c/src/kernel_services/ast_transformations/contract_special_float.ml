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

let is_special_float_term term =
  match term.term_node with
  | TLval (TVar {lv_name = "\\plus_infinity"}, _)
  | TLval (TVar {lv_name = "\\minus_infinity"}, _) ->
    Kernel.SpecialFloat.get () = "non-finite"
  | TLval (TVar {lv_name = "\\NaN"}, _) -> true
  | _ -> false

let rec is_special_float_pred pred =
  match pred.pred_content with
  | Pand (a, b) -> is_special_float_pred a || is_special_float_pred b
  | Por (a, b)  -> is_special_float_pred a && is_special_float_pred b
  | Papp (logic_info, [], [_]) ->
    begin
      match logic_info.l_var_info.lv_name with
      | "\\is_NaN" -> true
      | "\\is_plus_infinity" | "\\is_minus_infinity" | "\\is_infinite" ->
        Kernel.SpecialFloat.get () = "non-finite"
      | _ -> false
    end
  | Pnot {pred_content = Papp
              ({l_var_info = {lv_name = "\\is_finite"}}, [], [_])} ->
    true
  | Prel (Req, t1, t2) ->
    (is_special_float_term t1) <> (is_special_float_term t2)
  | _ -> false

let ensures_special_float = function
  | Normal, ip -> is_special_float_pred ip.ip_content.tp_statement
  | _ -> false

let negate_behavior_preconds bhv =
  let neg_preconds =
    List.map
      (fun e -> (Logic_const.pnot (e.ip_content.tp_statement)))
      (bhv.b_requires @ bhv.b_assumes)
  in
  let pred = Logic_const.pors neg_preconds in
  let name = "not_" ^ bhv.b_name in
  let pred = { pred with pred_name = name :: pred.pred_name } in
  Logic_const.new_predicate pred

let are_complete_disjoint spec behaviors =
  match spec.spec_complete_behaviors, spec.spec_disjoint_behaviors with
  | [complete], [disjoint] ->
    let mem bhv = List.(mem bhv.b_name complete && mem bhv.b_name disjoint) in
    List.for_all mem behaviors
  | _ -> false

let find_behavior name spec =
  let rec find acc = function
    | [] -> None, spec.spec_behavior
    | b :: tl -> if b.b_name = name then Some b, acc @ tl else find (b :: acc) tl
  in
  find [] spec.spec_behavior

let update_spec spec =
  let default, behaviors = find_behavior Cil.default_behavior_name spec in
  let filter bhv = List.exists ensures_special_float bhv.b_post_cond in
  let disabled, normal = List.partition filter behaviors in
  if disabled <> [] then
    match normal with
    | [ bhv ] when are_complete_disjoint spec behaviors ->
      let requires = bhv.b_requires @ bhv.b_assumes in
      let default =
        match default with
        | None ->
          bhv.b_name <- Cil.default_behavior_name;
          bhv.b_requires <- requires;
          bhv.b_assumes <- [];
          bhv
        | Some default ->
          default.b_requires <- default.b_requires @ requires;
          if bhv.b_assigns <> WritesAny
          then default.b_assigns <- bhv.b_assigns;
          if bhv.b_allocation <> FreeAllocAny
          then default.b_allocation <- bhv.b_allocation;
          default.b_post_cond <- default.b_post_cond @ bhv.b_post_cond;
          default.b_extended <- default.b_extended @ bhv.b_extended;
          default
      in
      spec.spec_behavior <- [default];
      spec.spec_complete_behaviors <- [];
      spec.spec_disjoint_behaviors <- [];
    | _ ->
      let requires = List.map negate_behavior_preconds disabled in
      let default =
        match default with
        | None -> Cil.mk_behavior ~requires ()
        | Some default ->
          default.b_requires <- default.b_requires @ requires;
          default
      in
      spec.spec_behavior <- default :: normal;
      let filter name = List.for_all (fun b -> b.b_name <> name) disabled in
      let map_filter = List.map (List.filter filter) in
      spec.spec_complete_behaviors <- map_filter spec.spec_complete_behaviors;
      spec.spec_disjoint_behaviors <- map_filter spec.spec_disjoint_behaviors

let visit_global = function
  | GFun (fundec, _) -> update_spec fundec.sspec
  | GFunDecl (spec, _, _) -> update_spec spec
  | _ -> ()

let run ast =
  if Kernel.SpecialFloat.get () <> "none" then
    Cil.iterGlobals ast visit_global

let transform =
  File.register_code_transformation_category "contract_special_float"

let () =
  File.add_code_transformation_before_cleanup
    ~deps:[(module Kernel.SpecialFloat)]
    transform run
