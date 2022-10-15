(**************************************************************************)
(*                                                                        *)
(*  This file is part of Aorai plug-in of Frama-C.                        *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*    INRIA (Institut National de Recherche en Informatique et en         *)
(*           Automatique)                                                 *)
(*    INSA  (Institut National des Sciences Appliquees)                   *)
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
open Logic_const
open Logic_utils
open Data_for_aorai
open Cil_types
open Cil_datatype
open Promelaast
open Bool3

let func_body_dkey = Aorai_option.register_category "func-body"
let action_dkey = Aorai_option.register_category "action"

let rename_pred v1 v2 p =
  let r =
    object
      inherit Visitor.frama_c_copy (Project.current())
      method! vlogic_var_use v =
        if Cil_datatype.Logic_var.equal v v1 then Cil.ChangeTo v2
        else Cil.JustCopy
    end
  in
  Visitor.visitFramacPredicate r p

(** Given a transition a function name and a function status (call or
    return) it returns if the cross condition can be satisfied with
    only function status.
*)
let isCrossable tr func st =
  let rec isCross p =
    match p with
    | TOr  (c1, c2) -> bool3or (isCross c1) (isCross c2)
    | TAnd (c1, c2) -> bool3and (isCross c1) (isCross c2)
    | TNot c1 -> bool3not (isCross c1)
    | TCall (kf,None) when Kernel_function.equal func kf && st=Call -> True
    | TCall (kf, Some _) when Kernel_function.equal func kf && st=Call ->
      Undefined
    | TCall _ -> False
    | TReturn kf when Kernel_function.equal func kf && st=Return -> True
    | TReturn _ -> False
    | TTrue -> True
    | TFalse -> False
    | TRel _ -> Undefined
  in
  let res = isCross tr.cross <> False in
  Aorai_option.debug ~level:2 "Function %a %s-state, \
                               transition %s -> %s is%s possible" Kernel_function.pretty func
    (if st=Call then "pre" else "post")
    tr.start.Promelaast.name
    tr.stop.Promelaast.name
    (if res then "" else " NOT");
  res

(** Returns the lval associated to the curState generated variable *)
let state_lval () =
  Cil.var (get_varinfo curState)

(* ************************************************************************* *)

let find_enum, set_enum =
  let module H =
    State_builder.Int_hashtbl
      (Cil_datatype.Enumitem)
      (struct
        let name = "ltl_states_enum"
        let size = 17
        let dependencies = (* TODO: projectify the automata
                              and depend on it.
                           *)
          [ Ast.self;
            Aorai_option.Ltl_File.self;
            Aorai_option.Buchi.self;
            Aorai_option.Ya.self
          ]
      end)
  in
  (fun n ->
     try H.find n
     with Not_found ->
       Aorai_option.fatal
         "Could not find the enum item corresponding to a state"),
  (List.iter (fun (n,item) -> H.add n item))

(* ************************************************************************* *)

(** Given a transition a function name and a function status (call or return)
    it returns if the cross condition can be satisfied with only
    function status. *)
let isCrossableAtInit tr func =
  (* When in doubt, return true anyway. More clever plug-ins will take care
     of analysing the instrumented code if needed. *)
  let eval_term_at_init t =
    if Kernel.LibEntry.get() then t
    else begin
      let bool_res test =
        if test then Cil.lconstant Integer.one else Cil.lzero ()
      in
      let bool3_res dft test =
        match test with
        | True -> bool_res true
        | False -> bool_res false
        | Undefined -> dft
      in
      let is_true t =
        match t with
        | TConst(Integer(i,_)) ->
          Bool3.bool3_of_bool (not (Integer.is_zero i))
        | TConst(LChr c) -> Bool3.bool3_of_bool (not (Char.code c <> 0))
        | TConst(LReal r) -> Bool3.bool3_of_bool (not (r.r_nearest <> 0.))
        | TConst(LStr _ | LWStr _) -> Bool3.True
        | _ -> Bool3.Undefined
      in
      let rec aux t =
        match t.term_node with
        | TConst (LEnum ei) ->
          aux (Logic_utils.expr_to_term ei.eival)
        | TLval lv ->
          (match aux_lv lv with
           | Some t -> t
           | None -> t)
        | TUnOp(op,t1) ->
          let t1 = aux t1 in
          (match op,t1.term_node with
           | Neg, TConst(Integer(i,_)) ->
             { t with term_node = TConst(Integer(Integer.neg i,None)) }
           | Neg, TConst(LReal r) ->
             let f = ~-. (r.r_nearest) in
             let r = {
               r_literal = string_of_float f ;
               r_nearest = f ;
               r_upper = ~-. (r.r_lower) ;
               r_lower = ~-. (r.r_upper) ;
             } in
             { t with term_node = TConst(LReal r) }
           | LNot, t1 ->  bool3_res t (is_true t1)
           | _ -> t)
        | TBinOp(op,t1,t2) ->
          let t1 = aux t1 in
          let t2 = aux t2 in
          let rec comparison comp t1 t2 =
            match t1.term_node,t2.term_node with
            | TConst (Integer(i1,_)), TConst (Integer(i2,_)) ->
              bool_res (comp (Integer.compare i1 i2))
            | TConst (LChr c1), TConst (LChr c2) ->
              bool_res (comp (Char.compare c1 c2))
            | TConst(LReal r1), TConst (LReal r2) ->
              bool_res (comp (compare r1.r_nearest r2.r_nearest))
            | TCastE(ty1,t1), TCastE(ty2,t2)
              when Cil_datatype.Typ.equal ty1 ty2 ->
              comparison comp t1 t2
            | _ -> t
          in
          (match op, t1.term_node, t2.term_node with

           | PlusA, TConst(Integer(i1,_)), TConst(Integer(i2,_)) ->
             { t with term_node =
                        TConst(Integer(Integer.add i1 i2,None))}
           | MinusA, TConst(Integer(i1,_)), TConst(Integer(i2,_)) ->
             { t with term_node =
                        TConst(Integer(Integer.sub i1 i2,None)) }
           | Mult, TConst(Integer(i1,_)), TConst(Integer(i2,_)) ->
             { t with term_node =
                        TConst(Integer(Integer.mul i1 i2,None)) }
           | Div, TConst(Integer(i1,_)), TConst(Integer(i2,_)) ->
             (try
                { t with term_node =
                           TConst(Integer(Integer.c_div i1 i2,None)) }
              with Division_by_zero -> t)
           | Mod, TConst(Integer(i1,_)), TConst(Integer(i2,_)) ->
             (try
                { t with term_node =
                           TConst(Integer(Integer.c_rem i1 i2,None)) }
              with Division_by_zero -> t)
           | Shiftlt, TConst(Integer(i1,_)), TConst(Integer(i2,_)) ->
             { t with term_node =
                        TConst(Integer(Integer.shift_left i1 i2,None)) }
           | Shiftrt, TConst(Integer(i1,_)), TConst(Integer(i2,_)) ->
             { t with term_node =
                        TConst(Integer(Integer.shift_right i1 i2,None)) }
           | Lt, _, _ -> comparison ((<) 0) t1 t2
           | Gt, _, _ -> comparison ((>) 0) t1 t2
           | Le, _, _ -> comparison ((<=) 0) t1 t2
           | Ge, _, _ -> comparison ((>=) 0) t1 t2
           | Eq, _, _ -> comparison ((=) 0) t1 t2
           | Ne, _, _ -> comparison ((<>) 0) t1 t2
           | LAnd, t1, t2 ->
             bool3_res t (Bool3.bool3and (is_true t1) (is_true t2))
           | LOr, t1, t2 ->
             bool3_res t (Bool3.bool3or (is_true t1) (is_true t2))
           | _ -> t)
        | TCastE(ty,t1) ->
          let t1 = aux t1 in
          (match t1.term_type with
             Ctype ty1 when Cil_datatype.Typ.equal ty ty1 -> t1
           | _ -> { t with term_node = TCastE(ty,t1) })
        | _ -> t
      and aux_lv (base,off) =
        match base with
        | TVar v ->
          (try
             Option.bind
               v.lv_origin
               (fun v ->
                  let init = Globals.Vars.find v in
                  let init = match init.Cil_types.init with
                      None -> Cil.makeZeroInit ~loc:v.vdecl v.vtype
                    | Some i -> i
                  in
                  aux_init off init)
           with Not_found -> None)
        | TMem t ->
          (match (aux t).term_node with
           | TAddrOf lv -> aux_lv (Logic_const.addTermOffsetLval off lv)
           | _ -> None)
        | TResult _ -> None
      and aux_init off initinfo =
        match off, initinfo with
        | TNoOffset, SingleInit e ->
          Some (aux (Logic_utils.expr_to_term e))
        | TIndex(t,oth), CompoundInit (ct,initl) ->
          (match (aux t).term_node with
           | TConst(Integer(i1,_)) ->
             Cil.foldLeftCompound ~implicit:true
               ~doinit:
                 (fun o i _ t ->
                    match o with
                    | Index({ enode = Const(CInt64(i2,_,_))},_)
                      when Integer.equal i1 i2 -> aux_init oth i
                    | _ -> t)
               ~ct ~initl ~acc:None
           | _ -> None)
        | TField(f1,oth), CompoundInit(ct,initl) ->
          Cil.foldLeftCompound ~implicit:true
            ~doinit:
              (fun o i _ t ->
                 match o with
                 | Field(f2,_) when Cil_datatype.Fieldinfo.equal f1 f2 ->
                   aux_init oth i
                 | _ -> t)
            ~ct ~initl ~acc:None
        | _ -> None
      in
      aux t
    end
  in
  let eval_rel_at_init rel t1 t2 =
    let t1 = eval_term_at_init (Cil.constFoldTerm true t1) in
    let t2 = eval_term_at_init (Cil.constFoldTerm true t2) in
    let comp =
      match rel with
      | Req -> ((=) 0)
      | Rneq -> ((<>) 0)
      | Rge -> ((>=) 0)
      | Rgt -> ((>) 0)
      | Rle -> ((<=) 0)
      | Rlt -> ((<) 0)
    in
    let rec comparison t1 t2 =
      match t1.term_node,t2.term_node with
      | TConst (Integer(i1,_)), TConst (Integer(i2,_)) ->
        Bool3.bool3_of_bool (comp (Integer.compare i1 i2))
      | TConst (LChr c1), TConst (LChr c2) ->
        Bool3.bool3_of_bool (comp (Char.compare c1 c2))
      | TConst(LReal r1), TConst (LReal r2) ->
        Bool3.bool3_of_bool (comp (compare r1.r_nearest r2.r_nearest))
      | TCastE(ty1,t1), TCastE(ty2,t2) when Cil_datatype.Typ.equal ty1 ty2 ->
        comparison t1 t2
      | _ -> Bool3.Undefined
    in
    comparison t1 t2
  in
  let rec isCross = function
    | TOr  (c1, c2) -> Bool3.bool3or (isCross c1) (isCross c2)
    | TAnd (c1, c2) -> Bool3.bool3and (isCross c1) (isCross c2)
    | TNot (c1) -> Bool3.bool3not (isCross c1)
    | TCall (s,None) -> Bool3.bool3_of_bool (Kernel_function.equal s func)
    | TCall (s, Some _) when Kernel_function.equal s func -> Undefined
    | TCall _ -> Bool3.False
    | TReturn _ -> Bool3.False
    | TTrue -> Bool3.True
    | TFalse -> Bool3.False
    | TRel(rel,t1,t2) -> eval_rel_at_init rel t1 t2

  in
  if Data_for_aorai.isObservableFunction func then begin
    match isCross tr.cross with
    | Bool3.True | Bool3.Undefined -> true
    | Bool3.False -> false
  end else true

(* ************************************************************************* *)
(** {b Expressions management} *)

(** Returns an int constant expression which represents the given int value. *)
let mk_int_exp value =
  new_exp ~loc:Cil_datatype.Location.unknown
    (Const(CInt64(Integer.of_int value,IInt,Some(string_of_int value))))

(** This function rewrites a cross condition into an ACSL expression.
    Moreover, by giving current operation name and its status (call or
    return) the generation simplifies the generated expression.
*)
let crosscond_to_pred cross curr_f curr_status =
  let check_current_event f status pred =
    if Kernel_function.equal curr_f f && curr_status = status then pred
    else (Bool3.False, pfalse)
  in
  let rec convert =
    function
    (* Lazy evaluation of logic operators if the result can be statically
       computed *)
    | TOr  (c1, c2) -> (*BinOp(LOr,convert c1,convert c2,Cil.intType)*)
      begin
        let (c1_val,c1_pred) = convert c1 in
        match c1_val with
        | Bool3.True      -> (c1_val,c1_pred)
        | Bool3.False     -> convert c2
        | Undefined ->
          let (c2_val,c2_pred) = convert c2 in
          match c2_val with
          | Bool3.True      -> (c2_val,c2_pred)
          | Bool3.False     -> (c1_val,c1_pred)
          | Undefined -> (Undefined,Logic_const.por(c1_pred, c2_pred))
      end

    | TAnd (c1, c2) -> (*BinOp(LAnd,convert c1,convert c2,Cil.intType)*)
      begin
        let (c1_val,c1_pred) = convert c1 in
        match c1_val with
        | Bool3.True      -> convert c2
        | Bool3.False     -> (c1_val,c1_pred)
        | Undefined ->
          let (c2_val,c2_pred) = convert c2 in
          match c2_val with
          | Bool3.True      -> (c1_val,c1_pred)
          | Bool3.False     -> (c2_val,c2_pred)
          | Undefined -> (Undefined,Logic_const.pand(c1_pred, c2_pred))
      end

    | TNot (c1)     -> (*UnOp(LNot,convert c1,Cil.intType)*)
      begin
        let (c1_val,c1_pred) = convert c1 in
        match c1_val with
        | Bool3.True      -> (Bool3.False,pfalse)
        | Bool3.False     -> (Bool3.True,ptrue)
        | Undefined -> (c1_val,Logic_const.pnot(c1_pred))
      end

    | TCall (f,b) ->
      let pred = match b with
          None -> Bool3.True, ptrue
        | Some b ->
          (Bool3.Undefined,
           Logic_const.pands
             (List.map Logic_const.pred_of_id_pred b.b_assumes))
      in
      check_current_event f Promelaast.Call pred
    | TReturn f ->
      check_current_event f Promelaast.Return (Bool3.True, ptrue)

    (* Other expressions are left unchanged *)
    | TTrue -> (Bool3.True, ptrue)
    | TFalse -> (Bool3.False, pfalse)
    | TRel(rel,t1,t2) ->
      (Bool3.Undefined, Logic_const.prel (rel,t1,t2))
  in
  snd (convert cross)

(* Translate a term into the correct expression at the location in argument.
   Be careful if you wish to re-use this function elsewhere, some cases are
   not treated generically.
   Used in crosscond_to_exp. *)

let rec term_to_exp t res =
  let loc = t.term_loc in
  match t.term_node with
  | TConst (Integer (value,repr)) -> Cil.kinteger64 ~loc ?repr value
  | TConst (LStr str) -> new_exp ~loc (Const (CStr str))
  | TConst (LWStr l) -> new_exp ~loc (Const (CWStr l))
  | TConst (LChr c) -> new_exp ~loc (Const (CChr c))
  | TConst (LReal l_real) ->
    (* r_nearest is by definition in double precision. *)
    new_exp ~loc (Const (CReal (l_real.r_nearest, FDouble, None)))
  | TConst (LEnum e) -> new_exp ~loc (Const (CEnum e))
  | TLval tlval -> new_exp ~loc (Lval (tlval_to_lval tlval res))
  | TSizeOf ty -> new_exp ~loc (SizeOf ty)
  | TSizeOfE t -> new_exp ~loc (SizeOfE(term_to_exp t res))
  | TSizeOfStr s -> new_exp ~loc (SizeOfStr s)
  | TAlignOf ty -> new_exp ~loc (AlignOf ty)
  | TAlignOfE t -> new_exp ~loc (AlignOfE (term_to_exp t res))
  | TUnOp (unop, t) ->
    new_exp ~loc (UnOp (unop, term_to_exp t res, Cil.intType))
  | TBinOp (binop, t1, t2)->
    new_exp ~loc
      (BinOp(binop, term_to_exp t1 res, term_to_exp t2 res, Cil.intType))
  | TCastE (ty, t) -> new_exp ~loc (CastE (ty, term_to_exp t res))
  | TAddrOf tlval -> new_exp ~loc (AddrOf (tlval_to_lval tlval res))
  | TStartOf tlval -> new_exp ~loc (StartOf (tlval_to_lval tlval res))
  | TLogic_coerce (_,t) -> term_to_exp t res
  | _ ->
    Aorai_option.fatal
      "Term %a cannot be transformed into exp."
      Printer.pp_term t

and tlval_to_lval (tlhost, toffset) res =
  let rec t_to_loffset t_offset = match t_offset with
      TNoOffset -> NoOffset
    | TField (f_i,t_off) -> Field(f_i, t_to_loffset t_off)
    | TIndex (t, t_off) -> Index (term_to_exp t res, t_to_loffset t_off)
    | TModel _ -> Aorai_option.fatal "TModel cannot be treated as exp."
  in
  match tlhost with
  | TVar l_var ->
    let v_info =
      begin
        match l_var.lv_origin with
        | Some vinfo -> vinfo
        | None -> Aorai_option.fatal "TVar not coming from a C Variable"
      end
    in
    (Var v_info, t_to_loffset toffset)
  |TMem t -> mkMem ~addr:(term_to_exp t res) ~off:(t_to_loffset toffset)
  |TResult _ ->
    (match res with
     | Some res -> Var res, t_to_loffset toffset
     (* This should not happen, as we always pass a real variable when
        generating body for a post-function when the original function
        has a non-void result. pre-functions and functions that return void
        should not see \result. *)
     | None -> Aorai_option.fatal "Unexpected \\result")

module Kf_bhv_cache =
  Datatype.Pair_with_collections(Cil_datatype.Kf)(Datatype.String)
    (struct let module_name = "Aorai_utils.Kf_bhv_cache" end)

let bhv_aux_functions_table = Kf_bhv_cache.Hashtbl.create 7

let get_bhv_aux_fct kf bhv =
  match
    Kf_bhv_cache.Hashtbl.find_opt bhv_aux_functions_table (kf,bhv.b_name)
  with
  | Some vi -> vi, false
  | None ->
    let loc = Cil_datatype.Location.unknown in
    let ovi = Kernel_function.get_vi kf in
    let vi = Cil_const.copy_with_new_vid ovi in
    vi.vname <- Data_for_aorai.get_fresh (ovi.vname ^ "_bhv_" ^ bhv.b_name);
    vi.vdefined <- false;
    vi.vghost <- true;
    let (_,args,varargs,_) = Cil.splitFunctionTypeVI ovi in
    let typ = TFun(Cil.intType, args, varargs,[]) in
    Cil.update_var_type vi typ;
    Cil.setFormalsDecl vi typ;
    vi.vattr <- [];
    let assoc =
      List.combine (Kernel_function.get_formals kf) (Cil.getFormalsDecl vi)
    in
    let vis = object
      inherit Visitor.frama_c_copy (Project.current())
      method! vlogic_var_use lv =
        match lv.lv_origin with
        | None -> JustCopy
        | Some vi ->
          (match
             List.find_opt (fun (x,_) -> Cil_datatype.Varinfo.equal vi x) assoc
           with
           | None -> JustCopy
           | Some (_,nvi) -> ChangeTo (Cil.cvar_to_lvar nvi))
    end
    in
    let assumes = Visitor.visitFramacPredicates vis bhv.b_assumes in
    let assumes = List.map Logic_const.refresh_predicate assumes in
    let assigns = Writes [] in
    let post_cond =
      [Normal,
       Logic_const.(
         new_predicate
           (prel (Req,tlogic_coerce (tresult Cil.intType) Linteger,lone())))]
    in
    let bhv_in =
      Cil.mk_behavior ~name:bhv.b_name ~assumes ~assigns ~post_cond ()
    in
    let name = bhv.b_name ^ "_out" in
    let assumes =
      [ Logic_const.(
            new_predicate (pnot (pands (List.map pred_of_id_pred assumes))))]
    in
    let assigns = Writes [] in
    let post_cond =
      [ Normal,
        Logic_const.(
          new_predicate
            (prel
               (Req, tlogic_coerce (tresult Cil.intType) Linteger, lzero())))]
    in
    let bhv_out = Cil.mk_behavior ~name ~assumes ~assigns ~post_cond () in
    Globals.Functions.replace_by_declaration (Cil.empty_funspec()) vi loc;
    let my_kf = Globals.Functions.get vi in
    Annotations.add_behaviors
      ~register_children:true Aorai_option.emitter my_kf [bhv_in; bhv_out];
    Annotations.add_assigns
      ~keep_empty:false Aorai_option.emitter my_kf (Writes []);
    Annotations.add_complete Aorai_option.emitter my_kf
      [bhv_in.b_name; bhv_out.b_name];
    Annotations.add_disjoint Aorai_option.emitter my_kf
      [bhv_in.b_name; bhv_out.b_name];
    vi, true

(** create a new abstract function call to decide whether we are in the
    corresponding behavior or not. *)
let mk_behavior_call generated_kf kf bhv =
  let aux,generated = get_bhv_aux_fct kf bhv in
  let res =
    Cil.makeLocalVar
      (Kernel_function.get_definition generated_kf)
      ~ghost:true ~referenced:true ~insert:false
      (get_fresh "bhv_aux") Cil.intType
  in
  let stmt =
    Cil.mkStmtOneInstr
      ~ghost:true
      ~valid_sid:true
      (Cil_types.Call (
          Some (Var res, NoOffset),
          Cil.evar aux,
          List.map (fun x -> Cil.evar x) (Kernel_function.get_formals kf),
          Cil_datatype.Location.unknown))
  in
  (res, stmt,
   if generated then Cil_datatype.Varinfo.Set.singleton aux
   else Cil_datatype.Varinfo.Set.empty)

(* Translate the cross condition of an automaton edge to an expression.
   Used in mk_stmt. This might generate calls to auxiliary functions, to
   take into account a guard that uses a function behavior. *)
let crosscond_to_exp generated_kf curr_f curr_status loc cond res =
  let check_current_event f status =
    Kernel_function.equal curr_f f && curr_status = status
  in
  let rel_convert = function
    | Rlt -> Lt
    | Rgt -> Gt
    | Rle -> Le
    | Rge -> Ge
    | Req -> Eq
    | Rneq -> Ne
  in
  let rec expnode_convert =
    function
    | TOr  (c1, c2) ->
      let stmts1, vars1, defs1, e1 = expnode_convert c1 in
      (match Cil.isInteger e1 with
       | None ->
         let stmts2, vars2, defs2, e2 = expnode_convert c2 in
         stmts1 @ stmts2, vars1 @ vars2,
         Cil_datatype.Varinfo.Set.union defs1 defs2,
         Cil.mkBinOp ~loc LOr e1 e2
       | Some i when Integer.is_zero i -> expnode_convert c2
       | Some _ -> [], [], Cil_datatype.Varinfo.Set.empty,e1)
    | TAnd (c1, c2) ->
      let stmts1, vars1, defs1, e1 = expnode_convert c1 in
      (match Cil.isInteger e1 with
       | None ->
         let stmts2, vars2, defs2, e2 = expnode_convert c2 in
         stmts1 @ stmts2, vars1 @vars2,
         Cil_datatype.Varinfo.Set.union defs1 defs2,
         Cil.mkBinOp ~loc LAnd e1 e2
       | Some i when Integer.is_zero i ->
         [], [], Cil_datatype.Varinfo.Set.empty, e1
       | Some _ -> expnode_convert c2)
    | TNot (c1) ->
      let stmts1, vars1, defs1, e1 = expnode_convert c1 in
      (match Cil.isInteger e1 with
       | None ->
         stmts1, vars1, defs1, Cil.new_exp ~loc (UnOp(LNot, e1,Cil.intType))
       | Some i when Integer.is_zero i ->
         [], [], Cil_datatype.Varinfo.Set.empty, Cil.one ~loc
       | Some _ -> [], [], Cil_datatype.Varinfo.Set.empty, Cil.zero ~loc)
    | TCall (f,None) ->
      if check_current_event f Promelaast.Call then
        [], [], Cil_datatype.Varinfo.Set.empty, Cil.one ~loc
      else
        [], [], Cil_datatype.Varinfo.Set.empty, Cil.zero ~loc
    | TCall (f, Some bhv) ->
      if check_current_event f Promelaast.Call then begin
        let res, stmt, new_kf = mk_behavior_call generated_kf f bhv in
        [ stmt ], [res], new_kf, Cil.evar res
      end else
        [], [], Cil_datatype.Varinfo.Set.empty, Cil.zero ~loc
    | TReturn f ->
      if check_current_event f Promelaast.Return then
        [], [], Cil_datatype.Varinfo.Set.empty, Cil.one ~loc
      else
        [], [], Cil_datatype.Varinfo.Set.empty, Cil.zero ~loc
    | TTrue -> [], [], Cil_datatype.Varinfo.Set.empty, Cil.one ~loc
    | TFalse -> [], [], Cil_datatype.Varinfo.Set.empty, Cil.zero ~loc
    | TRel(rel,t1,t2) ->
      [], [], Cil_datatype.Varinfo.Set.empty,
      Cil.mkBinOp
        ~loc (rel_convert rel) (term_to_exp t1 res) (term_to_exp t2 res)
  in
  expnode_convert cond

(* ************************************************************************* *)
(** {b Globals management} *)

(** Local copy of the file pointer *)
let file = ref Cil.dummyFile

let initFunction kf =
  let fname = Kernel_function.get_name kf in
  List.iter
    (fun vi -> set_paraminfo fname vi.vname vi)
    (Kernel_function.get_formals kf);
  match (Kernel_function.find_return kf).skind with
  | Cil_types.Return (Some { enode = Lval (Var vi,NoOffset) },_) ->
    set_returninfo fname vi (* Add the vi of return stmt *)
  | exception Kernel_function.No_Statement | _ -> () (* function without returned value *)

(** Copy the file pointer locally in the class in order to ease globals
    management and initializes some tables. *)
let initFile f =
  file := f;
  Data_for_aorai.setCData ();
  (* Adding C variables into our hashtable *)
  Globals.Vars.iter (fun vi _ -> set_varinfo vi.vname vi);
  Globals.Functions.iter initFunction

(** List of globals awaiting for adding into C file globals *)
let globals_queue = ref []

(** Flush all queued globals declarations into C file globals. *)
let flush_globals () =
  let before, after =
    List.fold_left
      (fun (b,a) elem ->
         match elem with
         | GFun(f,loc) as func ->
           (* [VP] if address of function is taken, it might be
              used in a global initializer: keep a declaration at this point
              to ensure ending up with a compilable C file in the end... *)
           let b =
             if f.svar.vaddrof then GFunDecl(Cil.empty_funspec(),f.svar,loc) :: b
             else b
           in
           b, func :: a
         | other -> other :: b, a)
      ([], [])
      !file.globals
  in
  !file.globals <- List.rev before @ List.rev !globals_queue @ List.rev after;
  Kernel_function.clear_sid_info ();
  globals_queue := []

let add_global glob = globals_queue := glob :: !globals_queue

(* Utilities for global variables *)
let add_gvar ?init vi =
  let initinfo = {Cil_types.init} in
  vi.vstorage <- NoStorage;
  add_global (GVar(vi,initinfo,vi.vdecl));
  Globals.Vars.add vi initinfo;
  set_varinfo vi.vname vi

let add_gvar_zeroinit vi =
  add_gvar ~init:(Cil.makeZeroInit ~loc:(CurrentLoc.get()) vi.vtype) vi

let mk_gvar ?init ~ty name =
  (* See if the variable is already declared *)
  let vi =
    try
      let ty' = typeAddAttributes [Attr ("ghost", [])] ty in
      let vi = Globals.Vars.find_from_astinfo name VGlobal in
      if not (Cil_datatype.Typ.equal vi.vtype ty') then
        Aorai_option.abort "Global %s is declared with type %a instead of %a"
          name Cil_printer.pp_typ vi.vtype Cil_printer.pp_typ ty';
      Globals.Vars.remove vi;
      vi
    with Not_found ->
      Cil.makeGlobalVar ~ghost:true name ty
  in
  add_gvar ?init vi

let mk_gvar_scalar ~init ?(ty = Cil.typeOf init) name =
  mk_gvar ~init:(SingleInit init) ~ty name

let mk_integer value =
  Cil.integer ~loc:(CurrentLoc.get()) value

(* Utilities for global enumerations *)
let mk_global_c_enum_type_tagged name elements_l =
  let einfo =
    { eorig_name = name;
      ename = name;
      eitems = [];
      eattr = [];
      ereferenced = true;
      ekind = IInt; }
  in
  let l =
    List.map
      (fun (e,i) ->
         { eiorig_name = e;
           einame = e;
           eival = mk_integer i;
           eiloc = Location.unknown;
           eihost = einfo})
      elements_l
  in
  einfo.eitems <- l;
  set_usedinfo name einfo;
  add_global (GEnumTag(einfo, Location.unknown));
  einfo

let mk_global_c_enum_type name elements =
  let _,elements =
    List.fold_left (fun (i,l) x -> (i+1,(x,i)::l)) (0,[]) elements
  in
  (* no need to rev the list, as the elements got their value already *)
  ignore (mk_global_c_enum_type_tagged name elements)

let mk_gvar_enum ?init name name_enuminfo =
  mk_gvar ?init ~ty:(TEnum(get_usedinfo name_enuminfo,[])) name


(* ************************************************************************* *)
(** {b Terms management / computation} *)

(** Return an integer constant term from the given value. *)
let mk_int_term value = Cil.lconstant (Integer.of_int value)

(** Returns a term representing the variable associated to the given varinfo *)
let mk_term_from_vi vi =
  Logic_const.term
    (TLval((Logic_utils.lval_to_term_lval (Cil.var vi))))
    (Ctype Cil.intType)

(** Given an lval term 'host' and an integer value 'off', it returns a lval term host[off]. *)
let mk_offseted_array host off =
  Logic_const.term
    (TLval(Logic_const.addTermOffsetLval (TIndex(mk_int_term (off),TNoOffset)) host))
    (Ctype Cil.intType)

let int2enumstate nums =
  let enum = find_enum nums in
  Logic_const.term (TConst (LEnum enum)) (Ctype (TEnum (enum.eihost,[])))

let int2enumstate_exp loc nums = new_exp ~loc (Const (CEnum (find_enum nums)))

(** Given an lval term 'host' and an integer value 'off', it returns a lval term host[off]. *)
let mk_offseted_array_states_as_enum host off =
  let enum = find_enum off in
  Logic_const.term
    (TLval
       (Logic_const.addTermOffsetLval
          (TIndex(Logic_const.term
                    (TConst(LEnum enum)) (Ctype (TEnum (enum.eihost,[]))),
                  TNoOffset))
          host))
    (Ctype Cil.intType)

(** Returns a lval term associated to the curState generated variable. *)
let host_state_term() = lval_to_term_lval (state_lval())
(*
(** Returns a lval term associated to the curStateOld generated variable. *)
let host_stateOld_term () =
  lval_to_term_lval ~cast:true (Cil.var (get_varinfo curStateOld))

(** Returns a lval term associated to the curTrans generated variable. *)
let host_trans_term () =
  lval_to_term_lval ~cast:true (Cil.var (get_varinfo curTrans))
*)
let state_term () =
  Logic_const.tvar (Cil.cvar_to_lvar (get_varinfo curState))

(*
let stateOld_term () =
  Logic_const.tvar (Cil.cvar_to_lvar (get_varinfo curStateOld))
let trans_term () =
  Logic_const.tvar (Cil.cvar_to_lvar (get_varinfo curTrans))
*)

(* Utilities for generation of predicates / statements / expression
   describing states' status. *)

let is_state_pred state =
  if Aorai_option.Deterministic.get () then
    Logic_const.prel (Req,state_term(),int2enumstate state.nums)
  else
    Logic_const.prel
      (Req,Cil.lone (),
       Logic_const.tvar (Data_for_aorai.get_state_logic_var state))

let is_state_non_det_stmt (_,copy) loc =
  mkStmtOneInstr ~ghost:true (Set (Cil.var copy, Cil.one ~loc, loc))

let is_state_det_stmt state loc =
  let var = Data_for_aorai.get_varinfo curState in
  mkStmtOneInstr
    ~ghost:true (Set (Cil.var var, int2enumstate_exp loc state.nums, loc))


let is_state_exp state loc =
  if Aorai_option.Deterministic.get ()
  then
    Cil.mkBinOp
      ~loc Eq
      (int2enumstate_exp loc state.nums)
      (Cil.evar ~loc (Data_for_aorai.get_varinfo curState))
  else
    Cil.mkBinOp
      ~loc Eq (Cil.evar (Data_for_aorai.get_state_var state)) (Cil.one ~loc)

let is_out_of_state_pred state =
  if Aorai_option.Deterministic.get () then
    Logic_const.prel (Rneq,state_term(),int2enumstate state.nums)
  else
    Logic_const.prel
      (Req,Cil.lzero (),
       Logic_const.tvar (Data_for_aorai.get_state_logic_var state))

(* In the deterministic case, we only assign the unique state variable
   to a specific enumerated constant. Non-deterministic automata on the other
   hand, need to have the corresponding state variable explicitly set to 0. *)
let is_out_of_state_stmt (_,copy) loc =
  if Aorai_option.Deterministic.get ()
  then
    Aorai_option.fatal
      "Deterministic automaton sync functions can't have out-of-state stmt. \
       Maybe this should use `is_out_of_state_exp' instead."
  else mkStmtOneInstr ~ghost:true (Set(Cil.var copy , mk_int_exp 0 , loc ))

let is_out_of_state_exp state loc =

  if Aorai_option.Deterministic.get ()
  then
    Cil.mkBinOp
      ~loc Ne
      (int2enumstate_exp loc state.nums)
      (evar ~loc (Data_for_aorai.get_varinfo curState))
  else
    Cil.mkBinOp
      ~loc Eq
      (Cil.evar (Data_for_aorai.get_state_var state))
      (mk_int_exp 0)

let assert_alive_automaton kf stmt =
  let pred =
    if Aorai_option.Deterministic.get() then
      let reject_state = Data_for_aorai.get_reject_state() in
      is_out_of_state_pred reject_state
    else begin
      let valid_states =
        List.filter
          (fun x -> not (Data_for_aorai.is_reject_state x))
          (fst (Data_for_aorai.getGraph ()))
      in
      let valid_preds = List.map is_state_pred valid_states in
      Logic_const.pors valid_preds
    end
  in
  let pred = { pred with pred_name = "aorai_smoke_test" :: pred.pred_name } in
  Annotations.add_assert Aorai_option.emitter ~kf stmt pred

(* Utilities for other globals *)

let mk_global_comment txt = add_global (GText (txt))

(* ************************************************************************* *)
(** {b Initialization management / computation} *)

let mk_global_states_init root =
  let (states,_ as auto) = Data_for_aorai.getGraph () in
  let states = List.sort Data_for_aorai.Aorai_state.compare states in
  let is_possible_init state =
    state.Promelaast.init = Bool3.True &&
    (let trans = Path_analysis.get_transitions_of_state state auto in
     List.exists (fun tr -> isCrossableAtInit tr root) trans)
  in
  List.iter
    (fun state ->
       let init =
         if is_possible_init state then mk_int_exp 1 else mk_int_exp 0
       in
       let init = SingleInit init in
       let var = Data_for_aorai.get_state_var state in
       add_gvar ~init var)
    states

class visit_decl_loops_init () =
  object(self)
    inherit Visitor.frama_c_inplace

    method! vstmt_aux stmt =
      begin
        match stmt.skind with
        | Loop _ ->
          let scope = Kernel_function.find_enclosing_block stmt in
          let f = Option.get self#current_func in
          let name = Data_for_aorai.loopInit ^ "_" ^ (string_of_int stmt.sid) in
          let typ =
            Cil.typeAddAttributes
              [Attr (Cil.frama_c_ghost_formal,[])] Cil.intType
          in
          let var = Cil.makeLocalVar ~ghost:true f ~scope name typ in
          Data_for_aorai.set_varinfo name var
        | _ -> ()
      end;
      Cil.DoChildren
  end

let mk_decl_loops_init () =
  let visitor = new visit_decl_loops_init ()  in
  Cil.visitCilFile (visitor :> Cil.cilVisitor) !file

let change_vars subst subst_res kf label pred =
  let add_label t = ChangeDoChildrenPost(t,fun t -> tat(t,label)) in
  let visitor =
    object
      inherit Visitor.frama_c_copy (Project.current())

      method! vterm t =
        match t.term_node with
          TLval (TVar { lv_origin = Some v},_) when v.vglob -> add_label t
        | TLval (TMem _,_) -> add_label t
        | _ -> DoChildren

      method! vterm_lhost = function
        | TResult ty ->
          (match kf with
             None -> Aorai_option.fatal
                       "found \\result without being at a Return event"
           | Some kf ->
             (try
                ChangeTo (TVar (Kernel_function.Hashtbl.find subst_res kf))
              with Not_found ->
                let new_lv =
                  Cil_const.make_logic_var_quant
                    ("__retres_" ^ (Kernel_function.get_name kf)) (Ctype ty)
                in
                Kernel_function.Hashtbl.add subst_res kf new_lv;
                ChangeTo (TVar new_lv)))
        | TMem _ | TVar _ -> DoChildren

      method! vlogic_var_use lv =
        match lv.lv_origin with
        | Some v when not v.vglob ->
          (try
             ChangeTo (Cil_datatype.Logic_var.Hashtbl.find subst lv)
           with Not_found ->
             let new_lv =
               Cil_const.make_logic_var_quant lv.lv_name lv.lv_type
             in
             Cil_datatype.Logic_var.Hashtbl.add subst lv new_lv;
             ChangeTo new_lv)
        | Some _ | None -> DoChildren
    end
  in Visitor.visitFramacPredicateNode visitor pred

let pred_of_condition subst subst_res label cond =
  let mk_func_event f =
    let op = tat (mk_term_from_vi (get_varinfo curOp),label) in
    (* [VP] TODO: change int to appropriate enum type. Also true
       elsewhere.
    *)
    let f =
      term
        (TConst (constant_to_lconstant (func_to_cenum f)))
        (Ctype (func_enum_type ()))
    in
    prel (Req,op,f)
  in
  let mk_func_status f status =
    let curr = tat (mk_term_from_vi (get_varinfo curOpStatus),label) in
    let call =
      term
        (TConst (constant_to_lconstant (op_status_to_cenum status)))
        (Ctype (status_enum_type()))
    in
    Logic_const.pand (mk_func_event f, prel(Req,curr,call))
  in
  let mk_func_start f = mk_func_status f Promelaast.Call in
  let mk_func_return f = mk_func_status f Promelaast.Return in
  let rec aux kf is_or = function
    | TOr(c1,c2) ->
      let kf, c1 = aux kf true c1 in
      let kf, c2 = aux kf true c2 in
      kf, Logic_const.por (c1, c2)
    | TAnd(c1,c2) ->
      let kf, c1 = aux kf false c1 in
      let kf, c2 = aux kf false c2 in
      kf, Logic_const.pand (c1, c2)
    | TNot c ->
      let kf, c = aux kf (not is_or) c in kf, Logic_const.pnot c
    | TCall (s,b) ->
      let pred = mk_func_start (Kernel_function.get_name s) in
      let pred =
        match b with
        | None -> pred
        | Some b ->
          Logic_const.pands
            (pred :: (List.map Logic_const.pred_of_id_pred b.b_assumes))
      in
      kf, pred
    | TReturn s ->
      let kf = if is_or then kf else Some s in
      kf, mk_func_return (Kernel_function.get_name s)
    | TTrue -> kf, ptrue
    | TFalse -> kf, pfalse
    | TRel(rel,t1,t2) ->
      kf,
      unamed (change_vars subst subst_res kf label (prel (rel,t1,t2)).pred_content)
  in
  snd (aux None true cond)

let mk_deterministic_lemma () =
  let automaton = Data_for_aorai.getGraph () in
  let make_one_lemma state =
    let label = Cil_types.FormalLabel "L" in
    let disjoint_guards acc trans1 trans2 =
      if trans1.numt <= trans2.numt then acc
      (* don't need to repeat the same condition twice*)
      else
        let subst = Cil_datatype.Logic_var.Hashtbl.create 5 in
        let subst_res = Kernel_function.Hashtbl.create 5 in
        let guard1 =
          pred_of_condition subst subst_res label trans1.cross
        in
        let guard2 =
          pred_of_condition subst subst_res label trans2.cross
        in
        let pred = Logic_const.pnot (Logic_const.pand (guard1, guard2)) in
        let quants =
          Cil_datatype.Logic_var.Hashtbl.fold
            (fun _ lv acc -> lv :: acc) subst []
        in
        let quants = Kernel_function.Hashtbl.fold
            (fun _ lv acc -> lv :: acc) subst_res quants
        in
        (* [VP] far from perfect, but should give oracles for
           regression tests that stay relatively stable across vid
           changes.  *)
        let quants =
          List.sort (fun v1 v2 -> String.compare v1.lv_name v2.lv_name) quants
        in
        Logic_const.pand (acc, (pforall (quants, pred)))
    in
    let trans = Path_analysis.get_transitions_of_state state automaton in
    let prop = Extlib.product_fold disjoint_guards ptrue trans trans in
    let prop = Logic_const.toplevel_predicate ~kind:Check prop in
    let name = state.Promelaast.name ^ "_deterministic_trans" in
    let lemma =
      Dlemma (name, [label],[],prop,[],Cil_datatype.Location.unknown)
    in
    Annotations.add_global Aorai_option.emitter lemma
  in
  List.iter make_one_lemma (fst automaton)

let make_enum_states () =
  let state_list =fst (Data_for_aorai.getGraph()) in
  let state_list =
    List.map (fun x -> (x.Promelaast.name, x.Promelaast.nums)) state_list
  in
  let enum = mk_global_c_enum_type_tagged states state_list in
  let mapping =
    List.map
      (fun (name,id) ->
         let item =
           List.find (fun y -> y.einame = name) enum.eitems
         in
         (id, item))
      state_list
  in
  set_enum mapping

let getInitialState () =
  let loc = Cil_datatype.Location.unknown in
  let states = fst (Data_for_aorai.getGraph()) in
  let s = List.find (fun x -> x.Promelaast.init = Bool3.True) states in
  Cil.new_exp ~loc (Const (CEnum (find_enum s.nums)))

(** This function computes all newly introduced globals (variables, enumeration structure, invariants, etc. *)
let initGlobals root complete =
  mk_global_comment "//****************";
  mk_global_comment "//* BEGIN Primitives generated for LTL verification";
  mk_global_comment "//* ";
  mk_global_comment "//* ";
  mk_global_comment "//* Some constants";
  if Aorai_option.Deterministic.get () then make_enum_states ();
  (* non deterministic mode uses one variable for each possible state *)
  mk_global_c_enum_type
    listOp
    (List.map
       (fun kf -> func_to_op_func (Kernel_function.get_name kf))
       (getObservablesFunctions() @ getIgnoredFunctions()));
  mk_gvar_enum curOp listOp;
  mk_global_c_enum_type  listStatus (callStatus::[termStatus]);
  mk_gvar_enum curOpStatus listStatus;

  mk_global_comment "//* ";
  mk_global_comment "//* States and Trans Variables";
  if Aorai_option.Deterministic.get () then begin
    mk_gvar_scalar ~init:(getInitialState()) curState;
    let init = getInitialState() (* TODO a distinct initial value for history *)
    and history = Data_for_aorai.whole_history () in
    List.iter (fun name -> mk_gvar_scalar ~init name) history
  end else
    mk_global_states_init root;

  if complete then begin
    mk_global_comment "//* ";
    mk_global_comment "//* Loops management";
    mk_decl_loops_init ();
  end;

  mk_global_comment "//* ";
  mk_global_comment "//****************** ";
  mk_global_comment "//* Auxiliary variables used in transition conditions";
  mk_global_comment "//*";
  List.iter add_gvar_zeroinit (Data_for_aorai.aux_variables());

  let auto = Data_for_aorai.getAutomata () in
  mk_global_comment "//* ";
  mk_global_comment "//****************** ";
  mk_global_comment "//* Metavariables";
  mk_global_comment "//*";
  Datatype.String.Map.iter (fun _ -> add_gvar_zeroinit) auto.metavariables;

  if Aorai_option.Deterministic.get () &&
     Aorai_option.GenerateDeterministicLemmas.get () then begin
    (* must flush now previous globals which are used in the lemmas in order to
       be able to put these last ones in the right places in the AST. *)
    flush_globals ();
    mk_deterministic_lemma ();
  end;

  (match Data_for_aorai.abstract_logic_info () with
   | [] -> ()
   | l ->
     let annot =
       Daxiomatic
         ("Aorai_pebble_axiomatic",
          List.map
            (fun li -> Dfun_or_pred(li,Cil_datatype.Location.unknown)) l,
          [],
          Cil_datatype.Location.unknown)
     in
     Annotations.add_global Aorai_option.emitter annot);
  mk_global_comment "//* ";
  mk_global_comment "//* END Primitives generated for LTL verification";
  mk_global_comment "//****************";

  flush_globals ()

(* ************************************************************************* *)
(** {b Pre/post management} *)

let automaton_locations loc =
  let auto_state =
    if Aorai_option.Deterministic.get () then
      [ Logic_const.new_identified_term (state_term()), FromAny ]
    else
      List.map
        (fun state ->
           Logic_const.new_identified_term
             (Logic_const.tvar
                (Data_for_aorai.get_state_logic_var state)), FromAny)
        (fst (Data_for_aorai.getGraph()))
  in
  (Logic_const.new_identified_term
     (Logic_const.tvar ~loc
        (Data_for_aorai.get_logic_var Data_for_aorai.curOpStatus)),
   FromAny) ::
  (Logic_const.new_identified_term
     (Logic_const.tvar ~loc
        (Data_for_aorai.get_logic_var Data_for_aorai.curOp)),
   FromAny) ::
  auto_state

let automaton_assigns loc = Writes (automaton_locations loc)

let aorai_assigns state loc =
  let merged_states =
    Aorai_state.Map.fold
      (fun _ state acc -> Data_for_aorai.merge_end_state state acc)
      state Aorai_state.Map.empty
  in
  let bindings =
    Aorai_state.Map.fold
      (fun _ (_,_,b) acc -> Data_for_aorai.merge_bindings b acc)
      merged_states Cil_datatype.Term.Map.empty
  in
  let elements =
    Cil_datatype.Term.Map.fold
      (fun t _ acc -> (Logic_const.new_identified_term t,FromAny)::acc)
      bindings []
  in
  Writes (automaton_locations loc @ elements)

let action_assigns trans =
  let add_if_needed v lv (known_vars, assigns as acc) =
    if Cil_datatype.Varinfo.Set.mem v known_vars then acc
    else
      Cil_datatype.Varinfo.Set.add v known_vars,
      (Logic_const.new_identified_term lv, FromAny)::assigns
  in
  let treat_one_action acc =
    function
    | Counter_init (host,off) | Counter_incr (host,off)
    | Copy_value ((host,off),_) ->
      let my_var =
        match host with
        | TVar ({ lv_origin = Some v}) -> v
        | _ -> Aorai_option.fatal "Auxiliary variable is not a C global"
      in
      let my_off =
        match off with
        | TNoOffset -> TNoOffset
        | TIndex _ -> TIndex(Logic_const.trange (None,None), TNoOffset)
        | TField _ | TModel _ ->
          Aorai_option.fatal "Unexpected offset in auxiliary variable"
      in
      add_if_needed my_var
        (Logic_const.term (TLval(host,my_off))
           (Cil.typeOfTermLval (host,my_off)))
        acc
    | Pebble_init(_,v,c) ->
      let cc = Option.get c.lv_origin in
      let cv = Option.get v.lv_origin in
      add_if_needed cv (Logic_const.tvar v)
        (add_if_needed cc (Logic_const.tvar c) acc)
    | Pebble_move(_,v1,_,v2) ->
      let cv1 = Option.get v1.lv_origin in
      let cv2 = Option.get v2.lv_origin in
      add_if_needed cv1 (Logic_const.tvar v1)
        (add_if_needed cv2 (Logic_const.tvar v2) acc)
  in
  let empty = (Cil_datatype.Varinfo.Set.empty,[]) in
  let empty_pebble =
    match trans.start.multi_state, trans.stop.multi_state with
    | Some(_,aux), None ->
      let caux = Option.get aux.lv_origin in
      add_if_needed caux (Logic_const.tvar aux) empty
    | _ -> empty
  in
  let _,res = List.fold_left treat_one_action empty_pebble trans.actions in
  Writes res

let get_reachable_trans state st auto current_state =
  match st with
  | Promelaast.Call ->
    (try
       let reach = Data_for_aorai.Aorai_state.Map.find state current_state in
       let treat_one_state end_state _ l =
         Path_analysis.get_edges state end_state auto @ l
       in
       Data_for_aorai.Aorai_state.Map.fold treat_one_state reach []
     with Not_found -> [])
  | Promelaast.Return ->
    let treat_one_state end_state (_,last,_) l =
      if Data_for_aorai.Aorai_state.Set.mem state last then
        Path_analysis.get_edges state end_state auto @ l
      else l
    in
    let treat_one_start _ map l =
      Data_for_aorai.Aorai_state.Map.fold treat_one_state map l
    in
    Data_for_aorai.Aorai_state.Map.fold treat_one_start current_state []

let get_reachable_trans_to state st auto current_state =
  match st with
  | Promelaast.Call ->
    let treat_one_start start map acc =
      if Data_for_aorai.Aorai_state.Map.mem state map then
        Path_analysis.get_edges start state auto @ acc
      else acc
    in
    Data_for_aorai.Aorai_state.Map.fold treat_one_start current_state []
  | Promelaast.Return ->
    let treat_one_state _ map acc =
      try
        let (_,last,_) = Data_for_aorai.Aorai_state.Map.find state map in
        Data_for_aorai.Aorai_state.Set.fold
          (fun start acc -> Path_analysis.get_edges start state auto @ acc)
          last acc
      with Not_found -> acc
    in Data_for_aorai.Aorai_state.Map.fold treat_one_state current_state []

(* force that we have a crossable transition for each state in which the
   automaton might be at current event. *)
let force_transition loc f st current_state =
  let (states, _ as auto) = Data_for_aorai.getGraph () in
  (* We iterate aux on all the states, to get
     - the predicate indicating in which states the automaton cannot possibly
       be before the transition (because we can't fire a transition from there).
     - the predicate indicating in which states the automaton might be, outside
       of the reject state
     - a list of predicate indicating for each possible state which condition
       must hold to have at least one possible transition.
  *)
  let aux (impossible_states,possible_states,has_crossable_trans) state =
    let reachable_trans = get_reachable_trans state st auto current_state in
    (* we inspect each transition originating from state, and maintain the
       following information:
       - a typed condition indicating under which condition a transition
         can be crossed from the current state
       - a flag indicating whether a transition that
         does not lead to a reject state can be crossed.
    *)
    let add_one_trans (has_crossable_trans, crossable_non_reject) trans =
      let has_crossable_trans =
        Logic_simplification.tor has_crossable_trans trans.cross
      in
      let crossable_non_reject =
        crossable_non_reject ||
        (isCrossable trans f st
         && not (Data_for_aorai.is_reject_state trans.stop))
      in has_crossable_trans, crossable_non_reject
    in
    let cond, crossable_non_reject =
      List.fold_left add_one_trans (Promelaast.TFalse, false) reachable_trans
    in
    let cond = fst (Logic_simplification.simplifyCond cond) in
    let cond = crosscond_to_pred cond f st in
    let start = is_state_pred state in
    if Logic_utils.is_trivially_false cond then begin
      (* no transition can be crossed. *)
      let not_start = is_out_of_state_pred state in
      Logic_const.pand ~loc (impossible_states,not_start),
      possible_states,
      has_crossable_trans
    end else begin
      (* we may cross a transition. Now check whether we have some
         condition to check for that. *)
      let has_crossable_trans =
        if Logic_utils.is_trivially_true cond then has_crossable_trans
        else
          Logic_const.new_predicate
            (pimplies ~loc (start,cond)) :: has_crossable_trans
      in
      let possible_states =
        (* reject_state must not be the only possible state *)
        match st with
        | Promelaast.Return ->
          if Data_for_aorai.is_reject_state state then possible_states
          else  Logic_const.por ~loc (possible_states,start)
        | Promelaast.Call ->
          if crossable_non_reject then
            Logic_const.por ~loc (possible_states, start)
          else possible_states
      in
      impossible_states, possible_states, has_crossable_trans
    end
  in
  let impossible_states, possible_states, crossable_trans =
    List.fold_left aux (ptrue, pfalse,[]) states
  in
  let states =
    if Aorai_option.Deterministic.get() then
      possible_states (* We're always in exactly one state, among the possible
                         ones, no need to list the impossible ones.
                      *)
    else (* requires that the cells for impossible states be '0' *)
      Logic_const.pand ~loc (possible_states, impossible_states)
  in
  Logic_const.new_predicate states :: (List.rev crossable_trans)

let partition_action trans =
  let add_state t st map =
    let old =
      try Cil_datatype.Term_lval.Map.find t map
      with Not_found -> Data_for_aorai.Aorai_state.Set.empty
    in
    let new_set = Data_for_aorai.Aorai_state.Set.add st old in
    Cil_datatype.Term_lval.Map.add t new_set map
  in
  let treat_one_action st acc =
    function
    | Counter_init t | Counter_incr t | Copy_value (t,_) -> add_state t st acc
    | Pebble_init _ | Pebble_move _ -> acc (* moving pebbles can occur at
                                              the same time (but not for
                                              same pebbles)
                                           *)
  in
  let treat_one_trans acc tr =
    List.fold_left (treat_one_action tr.start) acc tr.actions
  in
  List.fold_left treat_one_trans Cil_datatype.Term_lval.Map.empty trans

(* TODO: this must be refined to take pebbles into account: in that
   case, disjointedness condition is on pebble set for each state. *)
let disjoint_states loc _ states precond =
  let states = Data_for_aorai.Aorai_state.Set.elements states in
  let rec product acc l =
    match l with
    | [] -> acc
    | hd::tl ->
      let pairs = List.map (fun x -> (hd,x)) tl in
      product (pairs @ acc) tl
  in
  let disjoint = product [] states in
  List.fold_left
    (fun acc (st1, st2) ->
       Logic_const.new_predicate
         (Logic_const.por ~loc
            (is_out_of_state_pred st1,is_out_of_state_pred st2)) :: acc)
    precond
    disjoint

(*
forces that parent states of a state with action are mutually exclusive,
at least at pebble level.
*)
let incompatible_states loc st current_state =
  let (states,_ as auto) = Data_for_aorai.getGraph () in
  let aux precond state =
    let trans = get_reachable_trans_to state st auto current_state in
    let actions = partition_action trans in
    Cil_datatype.Term_lval.Map.fold (disjoint_states loc) actions precond
  in
  List.fold_left aux [] states

let auto_func_preconditions loc f st current_state =
  force_transition loc f st current_state @
  incompatible_states loc st current_state


let find_pebble_origin lab actions =
  let rec aux = function
    | [] -> Aorai_option.fatal "Transition to multi-state has no pebble action"
    | Pebble_init (_,_,count) :: _ ->
      Logic_const.term
        (TLval (TVar count, TNoOffset))
        (Logic_const.make_set_type count.lv_type)
    | Pebble_move (_,_,set,_) :: _-> Data_for_aorai.pebble_set_at set lab
    | _ :: tl -> aux tl
  in aux actions

let mk_sub ~loc pebble_set v =
  let sub = List.hd (Logic_env.find_all_logic_functions "\\subset") in
  Logic_const.papp ~loc
    (sub,[],
     [Logic_const.term ~loc (TLval (TVar v,TNoOffset)) pebble_set.term_type;
      pebble_set])

let pebble_guard ~loc pebble_set aux_var guard =
  let v = Cil_const.make_logic_var_quant aux_var.lv_name aux_var.lv_type in
  let g = rename_pred aux_var v guard in
  let g = Logic_const.pand ~loc (mk_sub ~loc pebble_set v, g) in
  Logic_const.pexists ~loc ([v], g)

let pebble_guard_neg ~loc pebble_set aux_var guard =
  let v = Cil_const.make_logic_var_quant aux_var.lv_name aux_var.lv_type in
  let g = rename_pred aux_var v guard in
  let g =
    Logic_const.pimplies ~loc
      (mk_sub ~loc pebble_set v, Logic_const.pnot ~loc g)
  in
  Logic_const.pforall ~loc ([v], g)

let pebble_post ~loc pebble_set aux_var guard =
  let v = Cil_const.make_logic_var_quant aux_var.lv_name aux_var.lv_type in
  let g = rename_pred aux_var v guard in
  let g = Logic_const.pimplies ~loc (mk_sub ~loc pebble_set v, g) in
  Logic_const.pforall ~loc ([v], g)

(* behavior is the list of all behaviors related to the given state, trans
   the list of potentially active transitions ending in this state.
   If the state is a multi-state, we have one behavior
   whose assumes is the disjunction of these assumes
*)
let add_behavior_pebble_actions ~loc f st behaviors state trans =
  match state.multi_state with
  | None -> behaviors
  | Some (set,aux) ->
    let name = Printf.sprintf "pebble_%s" state.name in
    let assumes =
      List.fold_left
        (fun acc b ->
           let assumes = List.map pred_of_id_pred b.b_assumes in
           Logic_const.por ~loc (acc, Logic_const.pands assumes))
        pfalse behaviors
    in
    let assumes = [ Logic_const.new_predicate assumes ] in
    let set = Data_for_aorai.pebble_set_at set Logic_const.here_label in
    let treat_action guard res action =
      match action with
      | Copy_value _ | Counter_incr _ | Counter_init _ ->
        res
      | Pebble_init (_,_,v) ->
        let a = Cil_const.make_logic_var_quant aux.lv_name aux.lv_type in
        let guard = rename_pred aux a guard in
        let guard =
          Logic_const.pand ~loc
            (Logic_const.prel
               ~loc (Req,Logic_const.tvar a,Logic_const.tvar v),
             guard)
        in
        Logic_const.term ~loc
          (Tcomprehension (Logic_const.tvar a,[a], Some guard))
          set.term_type
        :: res
      | Pebble_move(_,_,s1,_) ->
        let a = Cil_const.make_logic_var_quant aux.lv_name aux.lv_type in
        let guard = rename_pred aux a guard in
        let in_s =
          mk_sub ~loc
            (Data_for_aorai.pebble_set_at s1 Logic_const.pre_label) a
        in
        let guard = Logic_const.pand ~loc (in_s,guard) in
        Logic_const.term ~loc
          (Tcomprehension (Logic_const.tvar a,[a], Some guard))
          set.term_type
        :: res
    in
    let treat_one_trans acc tr =
      let guard = crosscond_to_pred tr.cross f st in
      let guard = Logic_const.pold guard in
      List.fold_left (treat_action guard) acc tr.actions
    in
    let res = List.fold_left treat_one_trans [] trans in
    let res = Logic_const.term (Tunion res) set.term_type in
    let post_cond =
      [ Normal, Logic_const.new_predicate (Logic_const.prel (Req,set,res))]
    in
    Cil.mk_behavior ~name ~assumes ~post_cond () :: behaviors

(* NB: we assume that the terms coming from YA automata keep quite simple.
   Notably that they do not introduce themselves any \at. *)
let make_old loc init t =
  let vis =
    object(self)
      inherit Visitor.frama_c_inplace
      val is_old = Stack.create ()
      method private is_old =
        if Stack.is_empty is_old then false else Stack.top is_old
      method! vterm t =
        match t.term_node with
        | TLval lv ->
          if Cil_datatype.Term_lval.Set.mem lv init then begin
            if self#is_old then begin
              Stack.push false is_old;
              DoChildrenPost
                (fun t ->
                   ignore (Stack.pop is_old);
                   Logic_const.(tat ~loc (t,here_label)))
            end else DoChildren
          end
          else begin
            if not self#is_old then begin
              Stack.push true is_old;
              DoChildrenPost
                (fun t ->
                   ignore (Stack.pop is_old);
                   Logic_const.told ~loc t)
            end else DoChildren
          end
        | _ -> DoChildren
    end
  in Visitor.visitFramacTerm vis t

let mk_action ~loc init a =
  let term_lval lv =
    Logic_const.term ~loc (TLval lv) (Cil.typeOfTermLval lv)
  in
  let add_lv lv = Cil_datatype.Term_lval.Set.add lv init in
  match a with
  | Counter_init lv ->
    [Logic_const.prel ~loc
       (Req, term_lval lv, Logic_const.tinteger ~loc 1)],
    add_lv lv
  | Counter_incr lv ->
    [Logic_const.prel ~loc
       (Req, term_lval lv,
        Logic_const.term ~loc
          (TBinOp (PlusA,
                   Logic_const.told ~loc (term_lval lv),
                   Logic_const.tinteger ~loc 1))
          (Cil.typeOfTermLval lv))],
    add_lv lv
  | Pebble_init _ | Pebble_move _ -> [],init (* Treated elsewhere *)
  | Copy_value (lv,t) ->
    [Logic_const.prel ~loc
       (Req, term_lval lv, make_old loc init t)],
    add_lv lv

let is_reachable state status =
  let treat_one_state _ map = Data_for_aorai.Aorai_state.Map.mem state map in
  Data_for_aorai.Aorai_state.Map.exists treat_one_state status

let concat_assigns a1 a2 =
  match a1,a2 with
  | WritesAny, _ -> a2
  | _, WritesAny -> a1
  | Writes l1, Writes l2 ->
    Writes
      (List.fold_left
         (fun acc (loc,_ as elt) ->
            if List.exists
                (fun (x,_) ->
                   Cil_datatype.Term.equal x.it_content loc.it_content)
                l2
            then
              acc
            else
              elt :: acc)
         l2 l1)

let get_accessible_transitions auto state status =
  let treat_one_state curr_state (_,last,_) acc =
    if Data_for_aorai.Aorai_state.equal curr_state state then
      Data_for_aorai.Aorai_state.Set.union last acc
    else acc
  in
  let treat_start_state _ map acc =
    Data_for_aorai.Aorai_state.Map.fold treat_one_state map acc
  in
  let previous_set =
    Data_for_aorai.Aorai_state.Map.fold
      treat_start_state status Data_for_aorai.Aorai_state.Set.empty
  in
  Data_for_aorai.Aorai_state.Set.fold
    (fun s acc -> Path_analysis.get_edges s state auto @ acc) previous_set []

let get_aux_var_bhv_name = function
  | TVar v, _ ->
    Data_for_aorai.get_fresh (v.lv_name ^ "_unchanged")
  | lv ->
    Aorai_option.fatal "unexpected lval for action variable: %a"
      Printer.pp_term_lval lv

(* Assumes that we don't have a multi-state here.
   pebbles are handled elsewhere
*)
let mk_unchanged_aux_vars_bhvs loc f st status =
  let (states,_ as auto) = Data_for_aorai.getGraph() in
  let add_state_trans acc state =
    let trans = get_reachable_trans state st auto status in
    List.rev_append trans acc
  in
  let crossable_trans =
    List.fold_left add_state_trans [] states
  in
  let add_trans_aux_var trans map = function
    | Counter_init lv | Counter_incr lv | Copy_value (lv,_) ->
      let other_trans =
        match Cil_datatype.Term_lval.Map.find_opt lv map with
        | Some l -> l
        | None -> []
      in
      Cil_datatype.Term_lval.Map.add lv (trans :: other_trans) map
    | Pebble_init _ | Pebble_move _ -> map
  in
  let add_trans_aux_vars map trans =
    List.fold_left (add_trans_aux_var trans) map trans.actions
  in
  let possible_actions =
    List.fold_left add_trans_aux_vars
      Cil_datatype.Term_lval.Map.empty
      crossable_trans
  in
  let out_trans trans =
    Logic_const.new_predicate
      (Logic_const.por ~loc
         (is_out_of_state_pred trans.start,
          Logic_const.pnot (crosscond_to_pred trans.cross f st)))
  in
  let mk_behavior lv trans acc =
    let name = get_aux_var_bhv_name lv in
    let assumes = List.map out_trans trans in
    let t = Data_for_aorai.tlval lv in
    let ot = Logic_const.told t in
    let p = Logic_const.prel (Req,t,ot) in
    let post_cond = [Normal, Logic_const.new_predicate p] in
    Cil.mk_behavior ~name ~assumes ~post_cond () :: acc
  in
  Cil_datatype.Term_lval.Map.fold mk_behavior possible_actions []

let mk_behavior ~loc auto kf e status state =
  Aorai_option.debug "analysis of state %s (%d)"
    state.Promelaast.name state.nums;
  if is_reachable state status then begin
    Aorai_option.debug "state %s is reachable" state.Promelaast.name;
    let my_trans = get_accessible_transitions auto state status in
    let rec treat_trans
        ((in_assumes, out_assumes, assigns, action_bhvs) as acc) l =
      match l with
      | [] -> acc
      | trans :: tl ->
        let consider, others =
          List.partition (fun x -> x.start.nums = trans.start.nums) tl

        in
        let start = is_state_pred trans.start in
        let not_start = is_out_of_state_pred trans.start in
        let in_guard, out_guard, assigns, my_action_bhvs =
          List.fold_left
            (fun (in_guard, out_guard, all_assigns, action_bhvs) trans ->
               Aorai_option.debug "examining transition %d" trans.numt;
               Aorai_option.debug "transition %d is active" trans.numt;
               let guard = crosscond_to_pred trans.cross kf e in
               let my_in_guard,my_out_guard =
                 match state.multi_state with
                 | None -> guard, Logic_const.pnot ~loc guard
                 | Some (_,aux) ->
                   let set =
                     find_pebble_origin Logic_const.here_label trans.actions
                   in
                   pebble_guard ~loc set aux guard,
                   pebble_guard_neg ~loc set aux guard
               in
               let out_guard =
                 Logic_const.pand ~loc (out_guard, my_out_guard)
               in
               let in_guard, all_assigns, action_bhvs =
                 match trans.actions with
                 | [] ->
                   (Logic_const.por ~loc (in_guard,my_in_guard),
                    all_assigns,
                    action_bhvs)
                 | _ ->
                   let name =
                     Printf.sprintf "buch_state_%s_in_%d"
                       state.name (List.length action_bhvs)
                   in
                   Aorai_option.debug "Name is %s" name;
                   let assumes = [
                     Logic_const.new_predicate
                       (Logic_const.pand ~loc (start,my_in_guard))
                   ]
                   in
                   let post_cond =
                     Normal,
                     Logic_const.new_predicate (is_state_pred state)
                   in
                   let treat_one_action (other_posts, init) a =
                     let posts, init = mk_action ~loc init a in
                     match state.multi_state  with
                     | None ->
                       other_posts @
                       List.map
                         (fun x ->
                            (Normal, Logic_const.new_predicate x))
                         posts,
                       init
                     | Some (_,aux) ->
                       let set =
                         find_pebble_origin
                           Logic_const.pre_label trans.actions
                       in
                       other_posts @
                       List.map
                         (fun x ->
                            (Normal,
                             Logic_const.new_predicate
                               (pebble_post ~loc set aux x)))
                         posts,
                       init
                   in
                   let post_cond,_ =
                     List.fold_left treat_one_action
                       ([post_cond], Cil_datatype.Term_lval.Set.empty)
                       trans.actions
                   in
                   let assigns = action_assigns trans in
                   let all_assigns = concat_assigns assigns all_assigns in
                   let bhv =
                     Cil.mk_behavior ~name ~assumes ~post_cond ()
                   in
                   in_guard, all_assigns, bhv :: action_bhvs
               in
               in_guard, out_guard, all_assigns, action_bhvs)
            (pfalse,ptrue,assigns, action_bhvs) (trans::consider)
        in
        treat_trans
          (Logic_const.por ~loc
             (in_assumes, (Logic_const.pand ~loc (start, in_guard))),
           Logic_const.pand ~loc
             (out_assumes,
              (Logic_const.por ~loc (not_start, out_guard))),
           assigns,
           my_action_bhvs
          )
          others
    in
    let my_trans = List.filter (fun x -> isCrossable x kf e) my_trans in
    let in_assumes, out_assumes, assigns, action_behaviors =
      treat_trans (pfalse, ptrue, WritesAny, []) my_trans
    in
    let behaviors =
      if Logic_utils.is_trivially_false in_assumes then action_behaviors
      else begin
        let behavior_in =
          Cil.mk_behavior
            ~name:(Printf.sprintf "buch_state_%s_in" state.Promelaast.name)
            ~assumes:[Logic_const.new_predicate in_assumes]
            ~post_cond:
              [Normal, Logic_const.new_predicate (is_state_pred state)]
            ()
        in behavior_in :: action_behaviors
      end
    in
    let behaviors =
      add_behavior_pebble_actions ~loc kf e behaviors state my_trans
    in
    let behaviors =
      if Logic_utils.is_trivially_false out_assumes then behaviors
      else begin
        let post_cond =
          match state.multi_state with
          | None -> [] (* Done elsewhere *)
          | Some (set,_) ->
            let set =
              Data_for_aorai.pebble_set_at set Logic_const.here_label
            in
            [Normal,
             Logic_const.new_predicate
               (Logic_const.prel ~loc
                  (Req,set,
                   Logic_const.term ~loc Tempty_set set.term_type))]
        in
        let post_cond =
          (Normal, (Logic_const.new_predicate (is_out_of_state_pred state)))
          :: post_cond
        in
        let behavior_out =
          Cil.mk_behavior
            ~name:(Printf.sprintf "buch_state_%s_out" state.Promelaast.name)
            ~assumes:[Logic_const.new_predicate out_assumes]
            ~post_cond ()
        in behavior_out :: behaviors
      end
    in
    assigns, behaviors
  end else begin
    Aorai_option.debug "state %s is not reachable" state.Promelaast.name;
    (* We know that we'll never end up in this state. *)
    let name = Printf.sprintf "buch_state_%s_out" state.Promelaast.name in
    let post_cond =
      match state.multi_state with
      | None -> []
      | Some (set,_) ->
        let set =
          Data_for_aorai.pebble_set_at set Logic_const.here_label
        in [Normal,
            Logic_const.new_predicate
              (Logic_const.prel ~loc
                 (Req,set,
                  Logic_const.term ~loc Tempty_set set.term_type))]
    in
    let post_cond =
      (Normal, Logic_const.new_predicate (is_out_of_state_pred state))
      ::post_cond
    in
    WritesAny,[mk_behavior ~name ~post_cond ()]
  end

let auto_func_behaviors loc f st state =
  let call_or_ret =
    match st with
    | Promelaast.Call -> "call"
    | Promelaast.Return -> "return"
  in
  Aorai_option.debug
    "func behavior for %a (%s)" Kernel_function.pretty f call_or_ret;
  let (states, _) as auto = Data_for_aorai.getGraph() in
  let requires = auto_func_preconditions loc f st state in
  let post_cond =
    let called_pre =
      Logic_const.new_predicate
        (Logic_const.prel ~loc
           (Req,
            Logic_const.tvar ~loc
              (Data_for_aorai.get_logic_var Data_for_aorai.curOpStatus),
            (Logic_const.term
               (TConst (constant_to_lconstant
                          (Data_for_aorai.op_status_to_cenum st)))
               (Ctype Cil.intType))))
    in
    let called_pre_2 =
      Logic_const.new_predicate
        (Logic_const.prel ~loc
           (Req,
            Logic_const.tvar ~loc
              (Data_for_aorai.get_logic_var Data_for_aorai.curOp),
            (Logic_const.term
               (TConst((constant_to_lconstant
                          (Data_for_aorai.func_to_cenum
                             (Kernel_function.get_name f)))))
               (Ctype Cil.intType))))
    in
    (* let old_pred = Aorai_utils.mk_old_state_pred loc in *)
    [(Normal, called_pre); (Normal, called_pre_2)]
  in
  let mk_behavior (assigns, behaviors) status =
    let new_assigns, new_behaviors =
      mk_behavior ~loc auto f st state status
    in
    concat_assigns new_assigns assigns, new_behaviors @ behaviors
  in
  let assigns = automaton_assigns loc in
  let assigns, behaviors = (List.fold_left mk_behavior (assigns,[]) states) in
  let global_behavior =
    Cil.mk_behavior ~requires ~post_cond ~assigns ()
  in
  let non_action_behaviors =
    mk_unchanged_aux_vars_bhvs loc f st state
  in
  (* Keep behaviors ordered according to the states they describe *)
  global_behavior :: (List.rev_append behaviors non_action_behaviors)

let mk_acceptance_pred () =
  let (st,_) = Data_for_aorai.getGraph () in
  List.fold_left
    (fun acc s ->
       match s.acceptation with
         Bool3.True -> Logic_const.por (acc, is_state_pred s)
       | Bool3.False | Bool3.Undefined -> acc)
    Logic_const.pfalse st

let mk_acceptance_bhv () =
  let accept = Logic_const.new_predicate (mk_acceptance_pred()) in
  let post_cond = [Normal, accept] in
  let name = "aorai_acceptance" in
  Cil.mk_behavior ~name ~post_cond ()

let act_convert loc act res =
  let treat_one_act =
    function
    | Counter_init t_lval ->
      Cil.mkStmtOneInstr
        ~ghost:true (Set (tlval_to_lval t_lval res, Cil.one ~loc, loc))
    | Counter_incr t_lval ->
      let my_lval = tlval_to_lval t_lval res in
      Cil.mkStmtOneInstr ~ghost:true
        (Set
           (my_lval,
            (Cil.mkBinOp
               ~loc
               PlusA
               (Cil.new_exp ~loc (Lval my_lval))
               (Cil.one ~loc)),
            loc))
    | Copy_value (t_lval, t) ->
      Cil.mkStmtOneInstr ~ghost:true
        (Set (tlval_to_lval t_lval res, term_to_exp t res, loc))
    | _ ->
      Aorai_option.fatal "Peebles not treated yet." (* TODO : Treat peebles. *)
  in
  List.map treat_one_act act

let mk_transitions_stmt generated_kf loc f st res trans =
  List.fold_right
    (fun trans
      (aux_stmts, aux_vars, new_funcs, exp_from_trans, stmt_from_action) ->
      let (tr_stmts, tr_vars, tr_funcs, exp) =
        crosscond_to_exp generated_kf f st loc trans.cross res
      in
      let cond = Cil.mkBinOp ~loc LAnd (is_state_exp trans.start loc) exp in
      (tr_stmts @ aux_stmts,
       tr_vars @ aux_vars,
       Cil_datatype.Varinfo.Set.union tr_funcs new_funcs,
       Cil.mkBinOp ~loc LOr exp_from_trans cond,
       (Cil.copy_exp cond, act_convert loc trans.actions res)
       :: stmt_from_action))
    trans
    ([],[],Cil_datatype.Varinfo.Set.empty, Cil.zero ~loc, [])

let mk_goto loc b =
  let ghost = true in
  match b.bstmts with
  | [] -> Cil.mkBlock []
  | [ { skind = Instr i } ] ->
    let s = mkStmtOneInstr ~ghost i in
    Cil.mkBlock [s]
  | [ { skind = Goto (s,_) }] ->
    let s' = mkStmt ~ghost (Goto (ref !s,loc)) in
    Cil.mkBlock [s']
  | s::_ ->
    s.labels <-
      (Label(Data_for_aorai.get_fresh "__aorai_label",loc,false)):: s.labels;
    let s' = mkStmt ~ghost (Goto (ref s,loc)) in
    Cil.mkBlock [s']

let normalize_condition loc cond block1 block2 =
  let rec aux cond b1 b2 =
    match cond.enode with
    | UnOp(LNot,e,_) -> aux e b2 b1
    | BinOp(LAnd,e1,e2,_) ->
      let b2' = mk_goto loc b2 in
      let b1'= Cil.mkBlock [aux e2 b1 b2'] in
      aux e1 b1' b2
    | BinOp(LOr,e1,e2,_) ->
      let b1' = mk_goto loc b1 in
      let b2' = Cil.mkBlock [aux e2 b1' b2] in
      aux e1 b1 b2'
    | _ ->
      Cil.mkStmt ~ghost:true (If(cond,b1,b2,loc))
  in
  aux cond block1 block2

let mkIfStmt loc exp1 block1 block2 =
  if Kernel.LogicalOperators.get() then
    Cil.mkStmt ~ghost:true (If (exp1, block1, block2, loc))
  else
    normalize_condition loc exp1 block1 block2


let mk_deterministic_stmt
    generated_kf loc auto f fst status ret state
    (other_stmts, other_funcs, other_vars, trans_stmts as res) =
  if is_reachable state status then begin
    let trans = get_accessible_transitions auto state status in
    let aux_stmts, aux_vars, aux_funcs, _, stmt_from_action =
      mk_transitions_stmt generated_kf loc f fst ret trans
    in
    let stmts =
      List.fold_left
        (fun acc (cond, stmt_act) ->
           [mkIfStmt loc cond
              (mkBlock (is_state_det_stmt state loc :: stmt_act))
              (mkBlock acc)])
        trans_stmts
        (List.rev stmt_from_action)
    in
    aux_stmts @ other_stmts,
    Cil_datatype.Varinfo.Set.union aux_funcs other_funcs,
    aux_vars @ other_vars,
    stmts
  end else res

(* mk_non_deterministic_stmt loc (states, tr) f fst status state
   Generates the statement updating the variable representing
   the state argument.
   If state is reachable, generates a "If then else" statement, else it is
   just an assignment.
   Used in auto_func_block. *)
let mk_non_deterministic_stmt
    generated_kf loc (states, tr) f fst status ((st,_) as state) res =
  if is_reachable st status then begin
    let useful_trans =  get_accessible_transitions (states,tr) st status in
    let aux_stmts, new_vars, new_funcs, cond,stmt_from_action =
      mk_transitions_stmt generated_kf loc f fst res useful_trans
    in
    let then_stmt = is_state_non_det_stmt state loc in
    let else_stmt = [is_out_of_state_stmt state loc] in
    let trans_stmts =
      let actions =
        List.fold_left
          (fun acc (cond, stmt_act) ->
             if stmt_act = [] then acc
             else
               (mkIfStmt loc cond (mkBlock stmt_act) (mkBlock []))::acc)
          []
          (List.rev stmt_from_action)
      in
      mkIfStmt loc cond (mkBlock [then_stmt]) (mkBlock else_stmt) :: actions
    in
    new_funcs, new_vars, aux_stmts @ trans_stmts
  end else
    Cil_datatype.Varinfo.Set.empty, [], [is_out_of_state_stmt state loc]

let equalsStmt lval exp loc = (* assignment *)
  Cil.mkStmtOneInstr ~ghost:true (Set (lval, exp, loc))

let mk_deterministic_body generated_kf loc f st status res =
  let (states, _ as auto) = Data_for_aorai.getGraph() in
  let aux_stmts, aux_funcs, aux_vars, trans_stmts =
    List.fold_right
      (mk_deterministic_stmt generated_kf loc auto f st status res)
      states
      ([], Cil_datatype.Varinfo.Set.empty, [],
       (* if all else fails, go to reject state. *)
       [is_state_det_stmt (Data_for_aorai.get_reject_state()) loc])
  in
  aux_funcs, aux_vars, aux_stmts @ trans_stmts

let mk_non_deterministic_body generated_kf loc f st status res =
  (* For the following tests, we need a copy of every state. *)
  let (states, _) as auto = Data_for_aorai.getGraph() in
  let copies, local_var =
    let bindings =
      List.map
        (fun st ->
           let state_var = Data_for_aorai.get_state_var st in
           let copy = Cil.copyVarinfo state_var (state_var.vname ^ "_tmp") in
           copy.vglob <- false;
           (st,copy))
        states
    in bindings, snd (List.split bindings)
  in
  let copies_update =
    List.map
      (fun (st,copy) ->
         equalsStmt (Cil.var copy)
           (Cil.evar ~loc (Data_for_aorai.get_state_var st)) loc)
      copies
  in
  let new_funcs, local_var, main_stmt =
    List.fold_left
      (fun (new_funcs, aux_vars, stmts) state ->
         let my_funcs, my_vars, my_stmts =
           mk_non_deterministic_stmt generated_kf loc auto f st status state res
         in
         Cil_datatype.Varinfo.Set.union my_funcs new_funcs,
         my_vars @ aux_vars,
         my_stmts@stmts )
      (Cil_datatype.Varinfo.Set.empty, local_var, [])
      copies
  in

  (* Finally, we replace the state var values by the ones computed in copies. *)
  let stvar_update =
    List.map
      (fun (state,copy) ->
         equalsStmt
           (Cil.var (Data_for_aorai.get_state_var state))
           (Cil.evar ~loc copy) loc)
      copies
  in
  new_funcs, local_var, copies_update @ main_stmt @ stvar_update

let auto_func_block generated_kf loc f st status res =
  let dkey = func_body_dkey in
  let call_or_ret =
    match st with
    | Promelaast.Call -> "call"
    | Promelaast.Return -> "return"
  in
  Aorai_option.debug
    ~dkey "func code for %a (%s)" Kernel_function.pretty f call_or_ret;

  let stmt_begin_list =
    [
      (* First statement : what is the current status : called or return ? *)
      equalsStmt
        (Cil.var (Data_for_aorai.get_varinfo Data_for_aorai.curOpStatus))
        (Cil.new_exp ~loc (Const (Data_for_aorai.op_status_to_cenum st))) loc;
      (* Second statement : what is the current operation,
         i.e. which function ?  *)
      equalsStmt
        (Cil.var (Data_for_aorai.get_varinfo Data_for_aorai.curOp))
        (Cil.new_exp ~loc
           (Const (Data_for_aorai.func_to_cenum (Kernel_function.get_name f))))
        loc
    ]
  and stmt_history_update =
    if Aorai_option.Deterministic.get () then
      let history = Data_for_aorai.whole_history ()
      and cur_state = Data_for_aorai.(get_varinfo curState) in
      let add_stmt (src,acc) dst_name =
        let dst = Data_for_aorai.get_varinfo dst_name in
        let stmt = equalsStmt (Cil.var dst) (Cil.evar ~loc src) loc in
        dst, stmt :: acc
      in
      snd (List.fold_left add_stmt (cur_state,[]) history)
    else if Aorai_option.InstrumentationHistory.get () > 0 then
      Aorai_option.fatal "history is not implemented for non-deterministic \
                          automaton"
    else []
  in
  let new_funcs, local_var, main_stmt =
    if Aorai_option.Deterministic.get() then
      mk_deterministic_body generated_kf loc f st status res
    else
      mk_non_deterministic_body generated_kf loc f st status res
  in
  let ret =
    Cil.mkStmt ~ghost:true ~valid_sid:true (Cil_types.Return(None,loc))
  in
  if Aorai_option.SmokeTests.get () then begin
    assert_alive_automaton generated_kf ret;
  end;
  let res_block =
    (Cil.mkBlock
       ( stmt_begin_list @ stmt_history_update @ main_stmt @ [ret]))
  in
  res_block.blocals <- local_var;
  Aorai_option.debug ~dkey "Generated body is:@\n%a"
    Printer.pp_block res_block;
  new_funcs,res_block,local_var

let get_preds_wrt_params_reachable_states state f status =
  let auto = Data_for_aorai.getGraph () in
  let treat_one_trans acc tr = Logic_simplification.tor acc tr.cross in
  let find_trans state prev tr =
    Path_analysis.get_edges prev state auto @ tr
  in
  let treat_one_state state (_,last,_) acc =
    let my_trans =
      Data_for_aorai.Aorai_state.Set.fold (find_trans state) last []
    in
    let cond = List.fold_left treat_one_trans TFalse my_trans in
    let (_,dnf) = Logic_simplification.simplifyCond cond in
    let cond = Logic_simplification.simplifyDNFwrtCtx dnf f status in
    let pred = crosscond_to_pred cond f status in
    Logic_const.pand (acc, pimplies (is_state_pred state, pred))
  in
  Data_for_aorai.Aorai_state.Map.fold treat_one_state state ptrue

let get_preds_wrt_params_reachable_states state f status =
  let merge_reachable_state _  = Data_for_aorai.merge_end_state in
  let reachable_states =
    Data_for_aorai.Aorai_state.Map.fold
      merge_reachable_state state Data_for_aorai.Aorai_state.Map.empty
  in
  get_preds_wrt_params_reachable_states reachable_states f status

let get_preds_pre_wrt_params f =
  let pre = Data_for_aorai.get_kf_init_state f in
  get_preds_wrt_params_reachable_states pre f Promelaast.Call

let get_preds_post_bc_wrt_params f =
  let post = Data_for_aorai.get_kf_return_state f in
  get_preds_wrt_params_reachable_states post f Promelaast.Return

let treat_val loc base range pred =
  let add term =
    if Cil.isLogicZero base then term
    else Logic_const.term
        (TBinOp (PlusA, Logic_const.tat (base,Logic_const.pre_label), term))
        Linteger
  in
  let add_cst i = add (Logic_const.tinteger i) in
  let res =
    match range with
    | Fixed i -> Logic_const.prel (Req,loc, add_cst i)
    | Interval(min,max) ->
      let min = Logic_const.prel (Rle, add_cst min, loc) in
      let max = Logic_const.prel (Rle, loc, add_cst max) in
      Logic_const.pand (min,max)
    | Bounded (min,max) ->
      let min = Logic_const.prel (Rle, add_cst min, loc) in
      let max = Logic_const.prel (Rle, loc, add max) in
      Logic_const.pand (min,max)
    | Unbounded min -> Logic_const.prel (Rle, add_cst min, loc)
    | Unknown -> Logic_const.ptrue (* nothing is known: the loc can
                                      take any value from then on. *)
  in
  Aorai_option.debug ~dkey:action_dkey "Action predicate: %a"
    Printer.pp_predicate res;
  Logic_const.por(pred,res)

let possible_states_preds state =
  let treat_one_state start map acc =
    let make_possible_state state _ acc =
      Logic_const.por (acc,is_state_pred state)
    in
    let possible_states =
      Data_for_aorai.Aorai_state.Map.fold make_possible_state map pfalse
    in
    Logic_const.pimplies
      (Logic_const.pat (is_state_pred start,Logic_const.pre_label),
       possible_states)
    :: acc
  in
  Data_for_aorai.Aorai_state.Map.fold treat_one_state state []

let update_to_pred ~start ~pre_state ~post_state location bindings =
  let loc = Cil_datatype.Location.unknown in
  let intv =
    Cil_datatype.Term.Map.fold
      (treat_val location) bindings Logic_const.pfalse
  in
  let pred =
    match post_state.multi_state with
    | None -> intv
    | Some(set,aux) ->
      (* [VP 2011-09-05] In fact, not all the pebble come from the considered
         pre-state. Will this lead to too strong post-conditions?
      *)
      let set = Data_for_aorai.pebble_set_at set Logic_const.here_label in
      pebble_post ~loc set aux intv
  in
  let guard =
    Logic_const.pand ~loc
      (Logic_const.pat ~loc (is_state_pred pre_state, start),
       is_state_pred post_state)
  in
  Logic_const.pimplies ~loc (guard, pred)

let action_to_pred ~start ~pre_state ~post_state bindings =
  let treat_one_loc loc vals acc =
    update_to_pred ~start ~pre_state ~post_state loc vals :: acc
  in
  Cil_datatype.Term.Map.fold treat_one_loc bindings []

let all_actions_preds start state =
  let treat_current_state pre_state post_state (_,_,bindings) acc =
    let my_bindings =
      action_to_pred ~start ~pre_state ~post_state bindings
    in
    my_bindings @ acc
  in
  let treat_start_state pre_state map acc =
    Data_for_aorai.Aorai_state.Map.fold
      (treat_current_state pre_state) map acc
  in
  Data_for_aorai.Aorai_state.Map.fold treat_start_state state []

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
