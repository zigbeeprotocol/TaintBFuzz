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
open Cil_datatype
module Error = Translation_error

(**************************************************************************)
(********************** Forward references ********************************)
(**************************************************************************)

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

(*****************************************************************************)
(************************** Auxiliary  functions* ****************************)
(*****************************************************************************)

(* @return true iff the result of the function is provided by reference as the
   first extra argument at each call *)
let result_as_extra_argument = Gmp_types.Z.is_t
(* TODO: to be extended to any compound type? E.g. returning a struct is not
   good practice... *)

(*****************************************************************************)
(****************** Generation of function bodies ****************************)
(*****************************************************************************)

(* Generate the block of code containing the statement assigning [e] to [ret_vi]
   (the result). *)
let generate_return_block ~loc env ret_vi e = match e.enode with
  | Lval (Var _, NoOffset) ->
    (* the returned value is a variable: Cil invariant preserved;
       no need of [ret_vi] *)
    let return_retres = Cil.mkStmt ~valid_sid:true (Return (Some e, loc)) in
    let b, env =
      Env.pop_and_get env return_retres ~global_clear:false Env.After
    in
    b.blocals <- b.blocals;
    b.bscoping <- true;
    b, env
  | _ ->
    (* the returned value is _not_ a variable: restore the invariant *)
    let init = AssignInit (SingleInit e) in
    let set =
      Cil.mkStmtOneInstr ~valid_sid:true (Local_init (ret_vi, init, loc))
    in
    let return =
      Cil.mkStmt ~valid_sid:true (Return (Some (Cil.evar ~loc ret_vi), loc))
    in
    let b, env = Env.pop_and_get env set ~global_clear:false Env.Middle in
    ret_vi.vdefined <- true;
    b.blocals <- ret_vi :: b.blocals;
    b.bstmts <- b.bstmts @ [ return ];
    b.bscoping <- true;
    b, env

(* Generate the function's body for predicates. *)
let pred_to_block ~loc kf env ret_vi p =
  let e, _, env = !predicate_to_exp_ref ~adata:Assert.no_data kf env p in
  (* for predicate, since the result is either 0 or 1, return it directly (it
     cannot be provided as extra argument *)
  generate_return_block ~loc env ret_vi e

(* Generate the function's body for terms. *)
let term_to_block ~loc kf env ret_ty ret_vi t =
  let e, _, env = !term_to_exp_ref ~adata:Assert.no_data kf env t in
  if Cil.isVoidType ret_ty then
    (* if the function's result is a GMP, it is the first parameter of the
       function (by reference). *)
    let set =
      let lv_star_ret = Cil.mkMem ~addr:(Cil.evar ~loc ret_vi) ~off:NoOffset in
      let star_ret = Smart_exp.lval ~loc lv_star_ret in
      Gmp.init_set ~loc lv_star_ret star_ret e
    in
    let return_void = Cil.mkStmt ~valid_sid:true (Return (None, loc)) in
    let b, env = Env.pop_and_get env set ~global_clear:false Env.Middle in
    b.bstmts <- b.bstmts @ [ return_void ];
    b.bscoping <- true;
    b, env
  else
    generate_return_block ~loc env ret_vi e

let generate_body ~loc kf env ret_ty ret_vi = function
  | LBterm t -> term_to_block ~loc kf env ret_ty ret_vi t
  | LBpred p -> pred_to_block ~loc kf env ret_vi p
  | LBnone |LBreads _ | LBinductive _ -> assert false

(* Generate a kernel function from a given logic info [li] *)
let generate_kf ~loc fname env ret_ty params_ty li =
  (* build the formal parameters *)
  let params, params_ty_vi =
    List.fold_right2
      (fun lvi pty (params, params_ty) ->
         let ty = match pty with
           | Typing.Gmpz ->
             (* GMP's integer are arrays: consider them as pointers in function's
                parameters *)
             Gmp_types.Z.t_as_ptr ()
           | Typing.C_integer ik -> TInt(ik, [])
           | Typing.C_float ik -> TFloat(ik, [])
           (* for the time being, no reals but rationals instead *)
           | Typing.Rational -> Gmp_types.Q.t ()
           | Typing.Real -> Error.not_yet "real number"
           | Typing.Nan -> Typing.typ_of_lty lvi.lv_type
         in
         (* build the formals: cannot use [Cil.makeFormal] since the function
            does not exist yet *)
         let vi = Cil.makeVarinfo false true lvi.lv_name ty in
         vi :: params, (lvi.lv_name, ty, []) :: params_ty)
      li.l_profile
      params_ty
      ([], [])
  in
  (* build the varinfo storing the result *)
  let res_as_extra_arg = result_as_extra_argument ret_ty in
  let ret_vi, ret_ty, params_with_ret, params_ty_with_ret =
    let vname = "__retres" in
    if res_as_extra_arg then
      let ret_ty_ptr = TPtr(ret_ty, []) (* call by reference *) in
      let vname = vname ^ "_arg" in
      let vi = Cil.makeVarinfo false true vname ret_ty_ptr in
      vi, Cil.voidType, vi :: params, (vname, ret_ty_ptr, []) :: params_ty_vi
    else
      Cil.makeVarinfo false false vname ret_ty, ret_ty, params, params_ty_vi
  in
  (* build the function's varinfo *)
  let vi =
    Cil.makeGlobalVar
      fname
      (TFun
         (ret_ty,
          Some params_ty_with_ret,
          false,
          li.l_var_info.lv_attr))
  in
  vi.vdefined <- true;
  (* create the fundec *)
  let fundec =
    { svar = vi;
      sformals = params_with_ret;
      slocals = []; (* filled later to break mutual dependencies between
                       creating this list and creating the kf *)
      smaxid = 0;
      sbody = Cil.mkBlock []; (* filled later; same as above *)
      smaxstmtid = None;
      sallstmts = [];
      sspec = Cil.empty_funspec () }
  in
  Cil.setMaxId fundec;
  let spec = Cil.empty_funspec () in
  (* register the definition *)
  Globals.Functions.replace_by_definition spec fundec loc;
  (* create the kernel function itself *)
  let kf = Globals.Functions.get fundec.svar in
  Annotations.register_funspec ~emitter:Options.emitter kf;
  (* closure generating the function's body.
     Delay its generation after filling the memoisation table (for termination
     of recursive function calls) *)
  let gen_body () =
    let env = Env.push env in
    (* fill the typing environment with the function's parameters
       before generating the code (code generation invokes typing) *)
    let env = Env.Local_vars.push_new env in
    let env =
      let add ty env =
        Env.Local_vars.add env ty
      in
      (* The list of parameters has to respect the order of the parameters to
         keep consistency with the typing. Hence the folding is on the right.
         This is acceptable since in practice functions have few parameters *)
      List.fold_right add params_ty env
    in
    let env =
      let add env lvi vi =
        let i = Interval.interv_of_typ vi.vtype in
        Interval.Env.add lvi i;
        Env.Logic_binding.add_binding env lvi vi
      in
      List.fold_left2 add env li.l_profile params
    in
    let assigns_from =
      try Some (Assigns.get_assigns_from ~loc env li.l_profile li.l_var_info)
      with Assigns.NoAssigns -> None
    in
    let assigned_var =
      Logic_const.new_identified_term
        (if res_as_extra_arg then
           Logic_utils.expr_to_term (Assigns.get_gmp_integer ~loc ret_vi)
         else
           Logic_const.tresult fundec.svar.vtype)
    in
    begin
      match assigns_from with
      | None -> ()
      | Some assigns_from ->
        let assigns_from =
          List.map
            (fun e ->
               Logic_const.new_identified_term
                 (Logic_utils.expr_to_term e))
            assigns_from
        in
        Annotations.add_assigns
          ~keep_empty:false
          Options.emitter
          ~behavior:Cil.default_behavior_name
          kf
          (Writes [ assigned_var , From assigns_from]);
    end;
    let b, env = generate_body ~loc kf env ret_ty ret_vi li.l_body in
    fundec.sbody <- b;
    (* add the generated variables in the necessary lists *)
    (* TODO: factorized the code below that add the generated vars with method
       [add_generated_variables_in_function] in the main visitor *)
    let vars =
      let l = Env.get_generated_variables env in
      if ret_vi.vdefined then
        (ret_vi, Env.LFunction kf) :: l
      else
        l
    in
    let locals, blocks =
      List.fold_left
        (fun (local_vars, block_vars as acc) (v, scope) -> match scope with
           | Env.LFunction kf' when Kernel_function.equal kf kf' ->
             v :: local_vars, block_vars
           | Env.LLocal_block kf' when Kernel_function.equal kf kf' ->
             v :: local_vars, block_vars
           | _ -> acc)
        (fundec.slocals, fundec.sbody.blocals)
        vars
    in
    fundec.slocals <- locals;
    fundec.sbody.blocals <- blocks;
    List.iter
      (fun lvi ->
         Interval.Env.remove lvi;
         ignore (Env.Logic_binding.remove env lvi))
      li.l_profile
  in
  vi, kf, gen_body

(**************************************************************************)
(***************************** Memoization ********************************)
(**************************************************************************)

(* for each logic_info, associate its possible profiles, i.e. the types of its
   parameters + the generated varinfo for the function *)
let memo_tbl:
  kernel_function Typing.Function_params_ty.Hashtbl.t Logic_info.Hashtbl.t
  = Logic_info.Hashtbl.create 7

let reset () = Logic_info.Hashtbl.clear memo_tbl

let add_generated_functions globals =
  let rec aux acc = function
    | [] ->
      acc
    | GAnnot(Dfun_or_pred(li, loc), _) as g :: l ->
      let acc = g :: acc in
      (try
         (* add the declarations close to its corresponding logic function or
            predicate *)
         let params = Logic_info.Hashtbl.find memo_tbl li in
         let add_fundecl kf acc =
           GFunDecl(Cil.empty_funspec (), Kernel_function.get_vi kf, loc)
           :: acc
         in
         aux
           (Typing.Function_params_ty.Hashtbl.fold_sorted
              (fun _ -> add_fundecl)
              params
              acc)
           l
       with Not_found ->
         aux acc l)
    | g :: l ->
      aux (g :: acc) l
  in
  let rev_globals = aux [] globals in
  (* add the definitions at the end of [globals] *)
  let add_fundec kf globals =
    let fundec =
      try Kernel_function.get_definition kf
      with Kernel_function.No_Definition -> assert false
    in
    GFun(fundec, Location.unknown) :: globals
  in
  let rev_globals =
    Logic_info.Hashtbl.fold_sorted
      (fun _ -> Typing.Function_params_ty.Hashtbl.fold_sorted
          (fun _ -> add_fundec))
      memo_tbl
      rev_globals
  in
  List.rev rev_globals

(* Generate (and memoize) the function body and create the call to the
   generated function. *)
let function_to_exp ~loc ?tapp fname env kf li params_ty args =
  let ret_ty =
    match tapp with
    | Some tapp -> Typing.get_typ ~lenv:(Env.Local_vars.get env) tapp
    | None  -> (Cil_types.TInt (IInt, []))
  in
  let gen tbl =
    let vi, kf, gen_body = generate_kf fname ~loc env ret_ty params_ty li in
    Typing.Function_params_ty.Hashtbl.add tbl params_ty kf;
    vi, gen_body
  in
  (* memoise the function's varinfo *)
  let fvi, gen_body =
    try
      let h = Logic_info.Hashtbl.find memo_tbl li in
      try
        let kf = Typing.Function_params_ty.Hashtbl.find h params_ty in
        Kernel_function.get_vi kf,
        (fun () -> ()) (* body generation already planified *)
      with Not_found -> gen h
    with Not_found ->
      let h = Typing.Function_params_ty.Hashtbl.create 7 in
      Logic_info.Hashtbl.add memo_tbl li h;
      gen h
  in
  (* the generation of the function body must be performed after memoizing the
     kernel function in order to handle recursive calls in finite time :-) *)
  gen_body ();
  (* create the function call for the tapp *)
  let mkcall vi =
    let mk_args types args =
      match types (* generated by E-ACSL: no need to unroll *) with
      | TFun(_, Some params, _, _) ->
        (* additional casts are necessary whenever the argument is GMP and the
           parameter is a (small) integralType: after handling the context in
           [Translate] through [add_cast], the GMP has been translated into a
           [long] (that is what provided the GMP API). This [long] must now be
           translated to the parameter's type. It cannot be done before since
           the exact type of the parameter is only computed when the function is
           generated *)
        List.map2
          (fun (_, newt, _) e -> Cil.mkCast ~force:false ~newt e)
          params
          args
      | _ -> assert false
    in
    if result_as_extra_argument ret_ty then
      let args = mk_args fvi.vtype (Cil.mkAddrOf ~loc (Cil.var vi) :: args) in
      Call(None, Cil.evar fvi, args, loc)
    else
      let args = mk_args fvi.vtype args in
      Call(Some (Cil.var vi), Cil.evar fvi, args, loc)
  in
  (* generate the varinfo storing the result of the call *)
  Env.new_var
    ~loc
    ~name:li.l_var_info.lv_name
    env
    kf
    tapp
    ret_ty
    (fun vi _ -> [ Cil.mkStmtOneInstr ~valid_sid:true (mkcall vi) ])

let raise_errors = function
  | LBnone ->
    Error.not_yet
      "logic functions or predicates with no definition nor reads clause"
  | LBreads _ ->
    Error.not_yet "logic functions or predicates performing read accesses"
  | LBinductive _ -> Error.not_yet "inductive logic functions"
  | LBterm _
  | LBpred _ -> ()

let app_to_exp ~adata ~loc ?tapp kf env ?eargs li targs =
  let fname = li.l_var_info.lv_name in
  (* build the varinfo (as an expression) which stores the result of the
     function call. *)
  let _, e, adata, env =
    if Builtins.mem li.l_var_info.lv_name then
      (* E-ACSL built-in function call *)
      let args, adata, env =
        match eargs with
        | None ->
          List.fold_right
            (fun targ (l, adata, env) ->
               let e, adata, env = !term_to_exp_ref ~adata kf env targ in
               e :: l, adata, env)
            targs
            ([], adata, env)
        | Some eargs ->
          if List.compare_lengths targs eargs <> 0 then
            Options.fatal
              "[Tapp] unexpected number of arguments when calling %s"
              fname;
          eargs, adata, env
      in
      let vi, e, env =
        Env.new_var
          ~loc
          ~name:(fname ^ "_app")
          env
          kf
          tapp
          (Misc.cty (Option.get li.l_type))
          (fun vi _ ->
             [ Smart_stmt.rtl_call ~loc
                 ~result:(Cil.var vi)
                 ~prefix:""
                 fname
                 args ])
      in
      vi, e, adata, env
    else
      begin
        raise_errors li.l_body;
        (* build the arguments and compute the integer_ty of the parameters *)
        let params_ty, args, adata, env =
          let eargs, adata, env =
            match eargs with
            | None ->
              List.fold_right
                (fun targ (eargs, adata, env) ->
                   let e, adata, env = !term_to_exp_ref ~adata kf env targ in
                   e :: eargs, adata, env)
                targs
                ([], adata, env)
            | Some eargs ->
              if List.compare_lengths targs eargs <> 0 then
                Options.fatal
                  "[Tapp] unexpected number of arguments when calling %s"
                  fname;
              eargs, adata, env
          in
          try
            List.fold_right2
              (fun targ earg (params_ty, args, adata, env) ->
                 let param_ty =
                   Typing.get_number_ty
                     ~lenv:(Env.Local_vars.get env)
                     targ
                 in
                 let e, env =
                   try
                     let ty = Typing.typ_of_number_ty param_ty in
                     Typed_number.add_cast
                       ~loc
                       env
                       kf
                       (Some ty)
                       Typed_number.C_number
                       (Some targ)
                       earg
                   with Typing.Not_a_number ->
                     earg, env
                 in
                 param_ty :: params_ty, e :: args, adata, env)
              targs eargs
              ([], [], adata ,env)
          with Invalid_argument _ ->
            Options.fatal
              "[Tapp] unexpected number of arguments when calling %s"
              fname
        in
        let gen_fname =
          Varname.get ~scope:Varname.Global (Functions.RTL.mk_gen_name fname)
        in
        let vi, e, env =
          function_to_exp ~loc ?tapp gen_fname env kf li params_ty args
        in
        vi, e, adata, env
      end
  in
  e, adata, env

(*
Local Variables:
compile-command: "make -C ../.."
End:
*)
