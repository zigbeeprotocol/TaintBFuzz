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

open Cil
open Cil_types
open Analyses_types

(**************************************************************************)
(********************** Forward references ********************************)
(**************************************************************************)

let translate_predicate_ref
  : (kernel_function -> Env.t -> toplevel_predicate -> Env.t) ref
  = Extlib.mk_fun "translate_predicate_ref"

let predicate_to_exp_ref
  : (adata:Assert.t ->
     kernel_function ->
     Env.t ->
     predicate ->
     exp * Assert.t * Env.t) ref
  =
  ref (fun ~adata:_ _kf _env _p ->
      Extlib.mk_labeled_fun "predicate_to_exp_ref")

let term_to_exp_ref
  : (adata:Assert.t ->
     kernel_function ->
     Env.t ->
     term ->
     exp * Assert.t * Env.t) ref
  =
  ref (fun ~adata:_ _kf _env _t -> Extlib.mk_labeled_fun "term_to_exp_ref")

(**************************************************************************)
(************************* Loop annotations *******************************)
(**************************************************************************)

let handle_annotations env kf stmt =
  match stmt.skind with
  | Loop(_, ({ bstmts = stmts } as blk), loc, cont, break) ->
    (* Loop variant, save the current value of the variant *)
    let stmts, env, variant =
      Error.handle
        (fun (stmts, env, _) ->
           match Env.top_loop_variant env with
           | Some (t, measure_opt) ->
             let env = Env.set_annotation_kind env Variant in
             let env = Env.push env in
             (* There cannot be bound logical variables since we cannot write
                loops inside logic functions or predicates, hence lenv is []*)
             Typing.type_term ~use_gmp_opt:true ~lenv:[] t;
             let ty = Typing.get_typ ~lenv:[] t in
             if Gmp_types.is_t ty then Error.not_yet "loop variant using GMP";
             let e, _, env = !term_to_exp_ref ~adata:Assert.no_data kf env t in
             let vi_old, e_old, env =
               Env.new_var
                 ~loc
                 ~scope:Varname.Function
                 ~name:"old_variant"
                 env
                 kf
                 (Some t)
                 ty
                 (fun _ _ -> [])
             in
             let stmt =
               Smart_stmt.assigns ~loc ~result:(Cil.var vi_old) e
             in
             let blk, env =
               Env.pop_and_get env stmt ~global_clear:false Env.Middle
             in
             let stmts = Smart_stmt.block_stmt blk :: stmts in
             stmts, env, Some (t, e_old, measure_opt)
           | None -> stmts, env, None)
        (stmts, env, None)
    in
    (* Auxiliary function to generate variant and invariant checks *)
    let rec aux (stmts, env) = function
      | [] -> begin
          (* No statements remaining in the loop: variant check *)
          let env = Env.set_annotation_kind env Variant in
          let lenv = Env.Local_vars.get env in
          match variant with
          | Some (t, e_old, Some measure) ->
            let env = Env.push env in
            let t_old = { t with term_node = t.term_node } in
            let tapp =
              { term_node = Tapp(measure, [], [t_old; t]);
                term_loc = loc;
                term_name = [];
                term_type = Linteger;}
            in
            Typing.type_term ~use_gmp_opt:true ~lenv tapp;
            let e, _, env = !term_to_exp_ref ~adata:Assert.no_data kf env t in
            let e_tapp, _, env =
              Logic_functions.app_to_exp
                ~adata:Assert.no_data
                ~loc
                ~tapp
                kf
                env
                ~eargs:[e_old; e]
                measure
                [t_old; t]
            in
            let msg =
              Format.asprintf
                "%s(old %a, %a)"
                measure.l_var_info.lv_name
                Printer.pp_term t_old
                Printer.pp_term t
            in
            let adata, env = Assert.empty ~loc kf env in
            let adata, env =
              Assert.register
                ~loc
                env
                (Format.asprintf "old %a" Printer.pp_term t_old)
                e_old
                adata
            in
            let adata, env =
              Assert.register
                ~loc
                env
                (Format.asprintf "current %a" Printer.pp_term t)
                e
                adata
            in
            let stmt, env =
              Assert.runtime_check_with_msg
                ~adata
                ~loc
                msg
                ~pred_kind:Assert
                Variant
                kf
                env
                e_tapp
            in
            let blk, env =
              Env.pop_and_get env stmt ~global_clear:false Env.Middle
            in
            let stmts = Smart_stmt.block_stmt blk :: stmts in
            stmts, env
          | Some (t, e_old, None) ->
            let env = Env.push env in
            let t_old = Logic_utils.expr_to_term e_old in
            let variant_pos =
              Logic_const.prel ~loc (Rge, t_old, Logic_const.tinteger ~loc 0)
            in
            Typing.type_named_predicate ~lenv variant_pos;
            let variant_pos_e, _, env =
              !predicate_to_exp_ref ~adata:Assert.no_data kf env variant_pos
            in
            let msg1 =
              Format.asprintf
                "(old %a) %a 0"
                Printer.pp_term t
                Printer.pp_relation Rge
            in
            let adata1, env = Assert.empty ~loc kf env in
            let adata1, env =
              Assert.register
                ~loc
                env
                (Format.asprintf "old %a" Printer.pp_term t)
                e_old
                adata1
            in
            let e_old_ge_zero_stmt, env =
              Assert.runtime_check_with_msg
                ~adata:adata1
                ~loc
                msg1
                ~pred_kind:Assert
                Variant
                kf
                env
                variant_pos_e
            in
            let variant_dec =
              Logic_const.prel ~loc (Rgt, t_old, t)
            in
            Typing.type_named_predicate ~lenv variant_dec;
            let variant_dec_e, _, env =
              !predicate_to_exp_ref ~adata:Assert.no_data kf env variant_dec
            in
            let msg2 =
              Format.asprintf
                "(old %a) > %a"
                Printer.pp_term t
                Printer.pp_term t
            in
            let adata2, env = Assert.with_data_from ~loc kf env adata1 in
            let adata2, env =
              if Options.Assert_print_data.get () then
                (* To be able to display to the user a meaningful message for
                   the old value and the current value, we need to retrieve the
                   expression for the term [t]. *)
                let e, _, env =
                  !term_to_exp_ref ~adata:Assert.no_data kf env t
                in
                Assert.register
                  ~loc
                  env
                  (Format.asprintf "current %a" Printer.pp_term t)
                  e
                  adata2
              else
                adata2, env
            in
            let e_old_gt_e_stmt, env =
              Assert.runtime_check_with_msg
                ~adata:adata2
                ~loc
                msg2
                ~pred_kind:Assert
                Variant
                kf
                env
                variant_dec_e
            in
            let stmt =
              Smart_stmt.block_from_stmts
                [ e_old_ge_zero_stmt;
                  e_old_gt_e_stmt ]
            in
            let blk, env =
              Env.pop_and_get env stmt ~global_clear:false Env.Middle
            in
            let stmts = Smart_stmt.block_stmt blk :: stmts in
            stmts, env
          | None ->
            stmts, env
        end
      | [ last ] ->
        (* Last statement of the loop: invariant check *)
        (* Optimisation to only verify invariant on a non-empty body loop. *)
        let invariants = Env.top_loop_invariants env in
        let env = Env.set_annotation_kind env Invariant in
        let env = Env.push env in
        let env =
          let translate_named_predicate = !translate_predicate_ref in
          List.fold_left (translate_named_predicate kf) env invariants
        in
        let blk, env =
          Env.pop_and_get env last ~global_clear:false Env.Before
        in
        aux (Smart_stmt.block last blk :: stmts, env) []
      | hd :: tl -> aux (hd :: stmts, env) tl
    in
    let stmts, env = aux ([], env) stmts in
    (* The loop annotations have been handled, the loop environment can be
       popped *)
    let env = Env.pop_loop env in
    let new_blk = { blk with bstmts = List.rev stmts } in
    { stmt with skind = Loop([], new_blk, loc, cont, break) }, env
  | _ ->
    stmt, env

(**************************************************************************)
(**************************** Nested loops ********************************)
(**************************************************************************)
let rec mk_nested_loops ~loc mk_innermost_block kf env lscope_vars =
  let lenv = Env.Local_vars.get env in
  let term_to_exp = !term_to_exp_ref ~adata:Assert.no_data in
  match lscope_vars with
  | [] ->
    mk_innermost_block env
  | Lvs_quantif(t1, rel1, logic_x, rel2, t2) :: lscope_vars' ->
    assert (rel1 == Rle && rel2 == Rlt);
    Typing.type_term ~use_gmp_opt:false ~lenv t1;
    Typing.type_term ~use_gmp_opt:false ~lenv t2;
    let ctx =
      let ty1 = Typing.get_number_ty ~lenv t1 in
      let ty2 = Typing.get_number_ty ~lenv t2 in
      Typing.join ty1 ty2
    in
    let t_plus_one ?ty t =
      (* whenever provided, [ty] is known to be the type of the result *)
      let tone = Cil.lone ~loc () in
      let res = Logic_const.term ~loc (TBinOp(PlusA, t, tone)) Linteger in
      Option.iter
        (fun ty ->
           Typing.unsafe_set tone ~ctx:ty ~lenv ctx;
           Typing.unsafe_set t ~ctx:ty ~lenv ctx;
           Typing.unsafe_set res ~lenv ty)
        ty;
      res
    in
    let ty =
      try Typing.typ_of_number_ty ctx
      with Typing.Not_a_number -> assert false
    in
    (* loop counter corresponding to the quantified variable *)
    let var_x, x, env = Env.Logic_binding.add ~ty env kf logic_x in
    let lv_x = var var_x in
    let env = match ctx with
      | Typing.C_integer _ -> env
      | Typing.Gmpz -> Env.add_stmt env (Gmp.init ~loc x)
      | Typing.(C_float _ | Rational | Real | Nan) -> assert false
    in
    (* build the inner loops and loop body *)
    let body, env =
      mk_nested_loops ~loc mk_innermost_block kf env lscope_vars'
    in
    (* initialize the loop counter to [t1] *)
    let e1, _, env = term_to_exp kf (Env.push env) t1 in
    let init_blk, env = Env.pop_and_get
        env
        (Gmp.affect ~loc:e1.eloc lv_x x e1)
        ~global_clear:false
        Env.Middle
    in
    (* generate the guard [x < t2] *)
    let block_to_stmt b = Smart_stmt.block_stmt b in
    let tlv = Logic_const.tvar ~loc logic_x in
    (* if [t2] is of the form [t2'+1], generate the guard [x <= t2']
       to avoid the extra addition (relevant when computing with GMP) *)
    let guard =
      match t2.term_node with
      | TBinOp (PlusA, t2_minus_one, {term_node = TConst(Integer (n, _))}) when Integer.is_one n ->
        Logic_const.term ~loc
          (TBinOp(Le, tlv, { t2_minus_one with term_node = t2_minus_one.term_node }))
          Linteger
      | _ ->
        (* must copy [t2] to force it being typed again *)
        Logic_const.term ~loc
          (TBinOp(Lt, tlv, { t2 with term_node = t2.term_node } ))
          Linteger
    in
    Typing.type_term ~use_gmp_opt:false ~lenv ~ctx:Typing.c_int guard;
    let guard_exp, _, env = term_to_exp kf (Env.push env) guard in
    let break_stmt = Smart_stmt.break ~loc:guard_exp.eloc in
    let guard_blk, env = Env.pop_and_get
        env
        (Smart_stmt.if_stmt
           ~loc:guard_exp.eloc
           ~cond:guard_exp
           (mkBlock [ mkEmptyStmt ~loc () ])
           ~else_blk:(mkBlock [ break_stmt ]))
        ~global_clear:false
        Env.Middle
    in
    let guard = block_to_stmt guard_blk in
    (* increment the loop counter [x++];
       previous typing ensures that [x++] fits type [ty] *)
    let tlv_one = t_plus_one ~ty:ctx tlv in
    let incr, _, env = term_to_exp kf (Env.push env) tlv_one in
    let next_blk, env = Env.pop_and_get
        env
        (Gmp.affect ~loc:incr.eloc lv_x x incr)
        ~global_clear:false
        Env.Middle
    in
    (* generate the whole loop *)
    let next = block_to_stmt next_blk in
    let guard_for_small_type_opt = Bound_variables.get_guard_for_small_type logic_x in
    let stmts, env = match guard_for_small_type_opt with
      | None ->
        guard :: body @ [ next ], env
      | Some p ->
        let adata, env = Assert.empty ~loc kf env in
        let e, adata, env =
          (* Even though p is considered a RTE, it was generated while
             typing the loop, and was already typed at this moment. Thus
             there is no need to type it again *)
          !predicate_to_exp_ref ~adata kf (Env.push env) p
        in
        let stmt, env =
          Assert.runtime_check
            ~adata
            ~pred_kind:Assert
            RTE
            kf
            env
            e
            p
        in
        let b, env = Env.pop_and_get env stmt ~global_clear:false Env.After in
        let guard_for_small_type = Smart_stmt.block_stmt b in
        guard_for_small_type :: guard :: body @ [ next ], env
    in
    let start = block_to_stmt init_blk in
    let stmt = mkStmt
        ~valid_sid:true
        (Loop(
            [],
            mkBlock stmts,
            loc,
            None,
            Some break_stmt))
    in
    (* remove logic binding before returning *)
    Env.Logic_binding.remove env logic_x;
    [ start ;  stmt ], env
  | Lvs_let(lv, t) :: lscope_vars' ->
    let ty = Typing.get_typ ~lenv t in
    let vi_of_lv, exp_of_lv, env = Env.Logic_binding.add ~ty env kf lv in
    let e, _, env = term_to_exp kf env t in
    let ty = Cil.typeOf e in
    let init_set =
      if Gmp_types.Q.is_t ty then Rational.init_set else Gmp.init_set
    in
    let let_stmt = init_set ~loc (Cil.var vi_of_lv) exp_of_lv  e in
    let stmts, env =
      mk_nested_loops ~loc mk_innermost_block kf env lscope_vars'
    in
    (* remove the logic binding now that the block is constructed *)
    Env.Logic_binding.remove env lv;
    (* return *)
    let_stmt :: stmts, env
  | Lvs_formal _ :: _ ->
    Error.not_yet
      "creating nested loops from formal variable of a logic function"
  | Lvs_global _ :: _ ->
    Error.not_yet
      "creating nested loops from global logic variable"

(*
Local Variables:
compile-command: "make -C ../.."
End:
*)
