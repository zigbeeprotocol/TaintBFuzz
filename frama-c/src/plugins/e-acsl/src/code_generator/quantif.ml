(**************************************************************************)
(*                                                                        *)
(*  This file is part of the Frama-C's E-ACSL plug-in.                    *)
(*                                                                        *)
(*  Copyright (C) 2012-2021                                               *)
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
open Cil
open Analyses_types

(** Forward reference for [Translate_predicates.to_exp]. *)
let predicate_to_exp_ref
  : (adata:Assert.t ->
     kernel_function ->
     Env.t ->
     predicate ->
     exp * Assert.t * Env.t) ref
  =
  ref (fun ~adata:_ _kf _env _p ->
      Extlib.mk_labeled_fun "predicate_to_exp_ref")


(* It could happen that the bounds provided for a quantified [lv] are empty
   in the sense that [min <= lv < max] but [min > max + 1]. In such cases, \true
   (or \false depending on the quantification) should be generated instead of
   nested loops.
   [has_empty_quantif_with_false_negative] partially detects such cases:
   Case 1: an empty quantification was detected for sure, return true.
   Case 2: we don't know, return false. *)
let rec has_empty_quantif_with_false_negative = function
  | [] ->
    (* case 2 *)
    false
  | (t1, _, t2) :: guards ->
    let iv1 = Interval.(extract_ival (infer t1)) in
    let iv2 = Interval.(extract_ival (infer t2)) in
    let lower_bound, _ = Ival.min_and_max iv1 in
    let _, upper_bound = Ival.min_and_max iv2 in
    begin
      match lower_bound, upper_bound with
      | Some lower_bound, Some upper_bound ->
        let res  = lower_bound >= upper_bound in
        res (* case 1 *) || has_empty_quantif_with_false_negative guards
      | None, _ | _, None ->
        has_empty_quantif_with_false_negative guards
    end

let () =
  Labels.has_empty_quantif_ref := has_empty_quantif_with_false_negative

module Label_ids =
  State_builder.Counter(struct let name = "E_ACSL.Label_ids" end)

let convert kf env loc ~is_forall quantif =
  (* guarded quantification over integers (or a subtype of integer) *)
  let bound_vars, goal =
    Error.retrieve_preprocessing
      "preprocessing of quantified predicate"
      Bound_variables.get_preprocessed_quantifier
      quantif
      Printer.pp_predicate
  in
  match has_empty_quantif_with_false_negative bound_vars, is_forall with
  | true, true ->
    Cil.one ~loc, env
  | true, false ->
    Cil.zero ~loc, env
  | false, _ ->
    begin
      (* create different "initial value", "found value" and guard expression
         for the predicate depending on the type of quantification *)
      let init_val, found_val, mk_guard =
        let z = zero ~loc in
        let o = one ~loc in
        if is_forall then o, z, fun x -> x
        else z, o, fun e -> Smart_exp.lnot ~loc:e.eloc e
      in
      (* transform [bound_vars] into [lscope_var list],
         and update logic scope in the process *)
      let lvs_guards, env = List.fold_right
          (fun (t1, lv, t2) (lvs_guards, env) ->
             let lvs = Lvs_quantif (t1, Rle, lv, Rlt, t2) in
             let env = Env.Logic_scope.extend env lvs in
             lvs :: lvs_guards, env)
          bound_vars
          ([], env)
      in
      let var_res, res, env =
        (* variable storing the result of the quantifier *)
        let name = if is_forall then "forall" else "exists" in
        Env.new_var
          ~loc
          ~name
          env
          kf
          None
          intType
          (fun v _ ->
             let lv = var v in
             [ Smart_stmt.assigns ~loc ~result:lv init_val ])
      in
      let end_loop_ref = ref dummyStmt in
      (* innermost block *)
      let mk_innermost_block env =
        (* innermost loop body: store the result in [res] and go out according
           to evaluation of the goal *)
        let predicate_to_exp = !predicate_to_exp_ref ~adata:Assert.no_data in
        let test, _, env = predicate_to_exp kf (Env.push env) goal in
        let then_blk = mkBlock [ mkEmptyStmt ~loc () ] in
        let else_blk =
          (* use a 'goto', not a simple 'break' in order to handle 'forall' with
             multiple binders (leading to imbricated loops) *)
          mkBlock
            [ Smart_stmt.assigns ~loc ~result:(var var_res) found_val;
              mkStmt ~valid_sid:true (Goto(end_loop_ref, loc)) ]
        in
        let blk, env =
          Env.pop_and_get
            env
            (Smart_stmt.if_stmt ~loc ~cond:(mk_guard test) then_blk ~else_blk)
            ~global_clear:false
            Env.After
        in
        let blk = Cil.flatten_transient_sub_blocks blk in
        [ Smart_stmt.block_stmt blk ], env
      in
      let stmts, env =
        Loops.mk_nested_loops ~loc mk_innermost_block kf env lvs_guards
      in
      let env =
        Env.add_stmt env (Smart_stmt.block_stmt (mkBlock stmts))
      in
      (* where to jump to go out of the loop *)
      let end_loop = mkEmptyStmt ~loc () in
      let label_name = "e_acsl_end_loop" ^ string_of_int (Label_ids.next ()) in
      let label = Label(label_name, loc, false) in
      end_loop.labels <- label :: end_loop.labels;
      end_loop_ref := end_loop;
      let env = Env.add_stmt env end_loop in
      res, env
    end

let quantif_to_exp kf env p =
  let loc = p.pred_loc in
  match p.pred_content with
  | Pforall _ ->
    convert kf env loc ~is_forall:true p
  | Pexists _ ->
    convert kf env loc ~is_forall:false p
  | _ -> assert false

(*
Local Variables:
compile-command: "make -C ../.."
End:
*)
