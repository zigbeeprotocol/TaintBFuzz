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

(** Generate C implementations of E-ACSL predicates. *)

open Cil_types
open Cil_datatype
open Analyses_types
let dkey = Options.Dkey.translation

(**************************************************************************)
(********************** Forward references ********************************)
(**************************************************************************)

let translate_rte_annots_ref
  : ((Format.formatter -> code_annotation -> unit) ->
     code_annotation ->
     kernel_function ->
     Env.t ->
     code_annotation list ->
     Env.t) ref
  =
  ref (fun _pp _elt _kf _env _l ->
      Extlib.mk_labeled_fun "translate_rte_annots_ref")

let translate_rte_exp_ref
  : (?filter:(code_annotation -> bool) ->
     kernel_function ->
     Env.t ->
     exp ->
     Env.t) ref
  =
  ref (fun ?filter:_ _kf _env _e ->
      Extlib.mk_labeled_fun "translate_rte_exp_ref")

(* ************************************************************************** *)
(* Transforming predicates into C expressions (if any) *)
(* ************************************************************************** *)

let relation_to_binop = function
  | Rlt -> Lt
  | Rgt -> Gt
  | Rle -> Le
  | Rge -> Ge
  | Req -> Eq
  | Rneq -> Ne

(* Convert an ACSL predicate into a corresponding C expression (if any) in the
   given environment. Also extend this environment which includes the generating
   constructs.
   If [inplace] is true, then the root predicate is immediately translated
   regardless of its label. Otherwise [Translate_ats] is used to retrieve the
   translation. *)
let rec predicate_content_to_exp ~adata ?(inplace=false) ?name kf env p =
  let loc = p.pred_loc in
  let lenv = Env.Local_vars.get env in
  Cil.CurrentLoc.set loc;
  match p.pred_content with
  | Pfalse -> Cil.zero ~loc, adata, env
  | Ptrue -> Cil.one ~loc, adata, env
  | Papp (_, _::_,_) -> Env.not_yet env "predicates with labels"
  | Papp (li, [], args) ->
    let e, adata, env =
      Logic_functions.app_to_exp ~adata ~loc kf env li args in
    let adata, env = Assert.register_pred ~loc env p e adata in
    e, adata, env
  | Pdangling _ -> Env.not_yet env "\\dangling"
  | Pobject_pointer _ -> Env.not_yet env "\\object_pointer"
  | Pvalid_function _ -> Env.not_yet env "\\valid_function"
  | Prel(rel, t1, t2) ->
    let ity =
      Typing.get_integer_op_of_predicate ~lenv p
    in
    Translate_utils.comparison_to_exp
      ~adata
      ~loc
      kf
      env
      ity
      (relation_to_binop rel)
      t1
      t2
      None
  | Pand(p1, p2) ->
    (* p1 && p2 <==> if p1 then p2 else false *)
    Extlib.flatten
      (Env.with_params_and_result
         ~rte:true
         ~f:(fun env ->
             let e1, adata, env1 = to_exp ~adata kf env p1 in
             let e2, adata, env2 =
               to_exp ~adata kf (Env.push env1) p2 in
             let res2 = e2, env2 in
             let env3 = Env.push env2 in
             let name = match name with None -> "and" | Some n -> n in
             Extlib.nest
               adata
               (Translate_utils.conditional_to_exp
                  ~name
                  ~loc
                  kf
                  None
                  e1
                  res2
                  (Cil.zero ~loc, env3))
           )
         env)
  | Por(p1, p2) ->
    (* p1 || p2 <==> if p1 then true else p2 *)
    Extlib.flatten
      (Env.with_params_and_result
         ~rte:true
         ~f:(fun env ->
             let e1, adata, env1 = to_exp ~adata kf env p1 in
             let env' = Env.push env1 in
             let e2, adata, env2 =
               to_exp ~adata kf (Env.push env') p2
             in
             let res2 = e2, env2 in
             let name = match name with None -> "or" | Some n -> n in
             Extlib.nest
               adata
               (Translate_utils.conditional_to_exp
                  ~name
                  ~loc
                  kf
                  None
                  e1
                  (Cil.one ~loc, env')
                  res2)
           )
         env)
  | Pxor _ -> Env.not_yet env "xor"
  | Pimplies(p1, p2) ->
    (* (p1 ==> p2) <==> !p1 || p2 *)
    to_exp
      ~adata
      ~name:"implies"
      kf
      env
      (Logic_const.por ~loc ((Logic_const.pnot ~loc p1), p2))
  | Piff(p1, p2) ->
    (* (p1 <==> p2) <==> (p1 ==> p2 && p2 ==> p1) *)
    to_exp
      ~adata
      ~name:"equiv"
      kf
      env
      (Logic_const.pand ~loc
         (Logic_const.pimplies ~loc (p1, p2),
          Logic_const.pimplies ~loc (p2, p1)))
  | Pnot p ->
    let e, adata, env = to_exp ~adata kf env p in
    Smart_exp.lnot ~loc e, adata, env
  | Pif(t, p2, p3) ->
    Extlib.flatten
      (Env.with_params_and_result
         ~rte:true
         ~f:(fun env ->
             let e1, adata, env1 = Translate_terms.to_exp ~adata kf env t in
             let e2, adata, env2 =
               to_exp ~adata kf (Env.push env1) p2 in
             let res2 = e2, env2 in
             let e3, adata, env3 =
               to_exp ~adata kf (Env.push env2) p3
             in
             let res3 = e3, env3 in
             Extlib.nest
               adata
               (Translate_utils.conditional_to_exp ~loc kf None e1 res2 res3)
           )
         env)
  | Plet(li, p) ->
    (* Translate the term registered to the \let logic variable *)
    let adata, env = Translate_utils.env_of_li ~adata ~loc kf env li in
    (* Register the logic var to the logic scope *)
    let lvs = Lvs_let(li.l_var_info, Misc.term_of_li li) in
    let env = Env.Logic_scope.extend env lvs in
    (* Translate the body of the \let *)
    let e, adata, env = to_exp ~adata kf env p in
    (* Remove the logic var from the logic scope *)
    let env = Env.Logic_scope.remove env lvs in
    Interval.Env.remove li.l_var_info;
    e, adata, env
  | Pforall _ | Pexists _ ->
    let e, env = Quantif.quantif_to_exp kf env p in
    let adata, env = Assert.register_pred ~loc env p e adata in
    e, adata, env
  | Pat(p', label) ->
    if inplace then
      to_exp ~adata kf env p'
    else
      Translate_ats.to_exp ~loc ~adata kf env (PoT_pred p) label
  | Pvalid_read(BuiltinLabel Here, t) as pc
  | (Pvalid(BuiltinLabel Here, t) as pc) ->
    let call_valid ~adata t p =
      let name = match pc with
        | Pvalid _ -> "valid"
        | Pvalid_read _ -> "valid_read"
        | _ -> assert false
      in
      let e, adata, env =
        Memory_translate.call_valid ~adata ~loc kf name Cil.intType env t p
      in
      let adata, env = Assert.register_pred ~loc env p e adata in
      e, adata, env
    in
    (* we already transformed \valid(t) into \initialized(&t) && \valid(t):
       now convert this right-most valid. *)
    call_valid ~adata t p
  | Pvalid _ -> Env.not_yet env "labeled \\valid"
  | Pvalid_read _ -> Env.not_yet env "labeled \\valid_read"
  | Pseparated tlist ->
    let env =
      List.fold_left
        (fun env t ->
           let name = "separated_guard" in
           let p = Logic_const.pvalid_read ~loc (BuiltinLabel Here, t) in
           let p = { p with pred_name = name :: p.pred_name } in
           let tp = Logic_const.toplevel_predicate ~kind:Assert p in
           let annot = Logic_const.new_code_annotation (AAssert ([],tp)) in
           Typing.preprocess_rte ~lenv:(Env.Local_vars.get env) annot;
           !translate_rte_annots_ref
             Printer.pp_code_annotation
             annot
             kf
             env
             [annot]
        )
        env
        tlist
    in
    let e, adata, env =
      Memory_translate.call_with_size
        ~adata
        ~loc
        kf
        "separated"
        Cil.intType
        env
        tlist
        p
    in
    let adata, env = Assert.register_pred ~loc env p e adata in
    e, adata, env
  | Pinitialized(BuiltinLabel Here, t) ->
    let e, adata, env =
      (match t.term_node with
       (* optimisation when we know that the initialisation is ok *)
       | TAddrOf (TResult _, TNoOffset) -> Cil.one ~loc, adata, env
       | TAddrOf (TVar { lv_origin = Some vi }, TNoOffset)
         when
           vi.vformal || vi.vglob || Functions.RTL.is_generated_name vi.vname ->
         Cil.one ~loc, adata, env
       | _ ->
         let e, adata, env =
           Memory_translate.call_with_size
             ~adata
             ~loc
             kf
             "initialized"
             Cil.intType
             env
             [ t ]
             p
         in
         let adata, env = Assert.register_pred ~loc env p e adata in
         e, adata, env)
    in
    e, adata, env
  | Pinitialized _ -> Env.not_yet env "labeled \\initialized"
  | Pallocable _ -> Env.not_yet env "\\allocate"
  | Pfreeable(BuiltinLabel Here, t) ->
    let e, adata, env =
      Memory_translate.call ~adata ~loc kf "freeable" Cil.intType env t
    in
    let adata, env = Assert.register_pred ~loc env p e adata in
    e, adata, env
  | Pfreeable _ -> Env.not_yet env "labeled \\freeable"
  | Pfresh _ -> Env.not_yet env "\\fresh"

(** [to_exp ~adata ?inplace ?name kf ?rte env p] converts an ACSL predicate into
    a corresponding C expression.
    - [adata]: assertion context.
    - [inplace]: if the root predicate has a label, indicates if it should be
      immediately translated or if [Translate_ats] should be used to retrieve
      the translation.
    - [name]: name to use for generated variables.
    - [kf]: the enclosing function.
    - [rte]: if true, generate and translate RTE before translating the
      predicate.
    - [env]: the current environment.
    - [p]: the predicate to translate. *)
and to_exp ~adata ?inplace ?name kf ?rte env p =
  let p = Logic_normalizer.get_pred p in
  let rte = match rte with None -> Env.generate_rte env | Some b -> b in
  Extlib.flatten
    (Env.with_params_and_result
       ~rte:false
       ~f:(fun env ->
           let e, adata, env =
             predicate_content_to_exp ?inplace ~adata ?name kf env p
           in
           let env = if rte then !translate_rte_exp_ref kf env e else env in
           let cast =
             Typing.get_cast_of_predicate
               ~lenv:(Env.Local_vars.get env)
               p
           in
           Extlib.nest
             adata
             (Typed_number.add_cast
                ~loc:p.pred_loc
                ?name
                env
                kf
                cast
                Typed_number.C_number
                None
                e)
         )
       env)

let generalized_untyped_to_exp ~adata ?name kf ?rte env p =
  (* If [rte] is true, it means we're translating the root predicate of an
     assertion and we need to generate the RTE for it. The typing environment
     must be cleared. Otherwise, if [rte] is false, it means we're already
     translating RTE predicates as part of the translation of another root
     predicate, and the typing environment must be kept. *)
  let rte = match rte with None -> Env.generate_rte env | Some b -> b in
  let e, adata, env = to_exp ~adata ?name kf ~rte env p in
  assert (Typ.equal (Cil.typeOf e) Cil.intType);
  let env = Env.Logic_scope.reset env in
  e, adata, env

let do_it ?pred_to_print kf env p =
  match p.tp_kind with
  | Assert | Check ->
    Options.feedback ~dkey ~level:3 "translating predicate %a"
      Printer.pp_toplevel_predicate p;
    let pred_to_print =
      match pred_to_print with
      | Some pred ->
        Options.feedback ~dkey ~level:3 "(predicate to print %a)"
          Printer.pp_predicate pred;
        pred
      | None -> p.tp_statement
    in
    let adata, env = Assert.empty ~loc:p.tp_statement.pred_loc kf env in
    let e, adata, env =
      generalized_untyped_to_exp ~adata kf env p.tp_statement
    in
    let stmt, env =
      Assert.runtime_check
        ~adata
        ~pred_kind:p.tp_kind
        (Env.annotation_kind env)
        kf
        env
        e
        pred_to_print
    in
    Env.add_stmt env stmt
  | Admit -> env

let predicate_to_exp_without_rte ~adata kf env p =
  (* forget optional argument ?rte and ?name*)
  to_exp ~adata kf env p

let predicate_to_exp_without_inplace ~adata ?name kf ?rte env p =
  to_exp ~adata ?name kf ?rte env p

let () =
  Translate_utils.predicate_to_exp_ref := predicate_to_exp_without_inplace;
  Translate_ats.predicate_to_exp_ref := to_exp;
  Loops.translate_predicate_ref := do_it;
  Loops.predicate_to_exp_ref := predicate_to_exp_without_rte;
  Quantif.predicate_to_exp_ref := predicate_to_exp_without_rte;
  Memory_translate.predicate_to_exp_ref := predicate_to_exp_without_rte;
  Logic_functions.predicate_to_exp_ref := predicate_to_exp_without_rte

exception No_simple_translation of predicate

(* This function is used by Guillaume.
   However, it is correct to use it only in specific contexts. *)
let untyped_to_exp p =
  let env = Env.push Env.empty in
  let env = Env.set_rte env false in
  let e, _, env =
    try generalized_untyped_to_exp
          ~adata:Assert.no_data
          (Kernel_function.dummy ())
          env
          p
    with Rtl.Symbols.Unregistered _ -> raise (No_simple_translation p)
  in
  if not (Env.has_no_new_stmt env)
  then raise (No_simple_translation p);
  e

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
