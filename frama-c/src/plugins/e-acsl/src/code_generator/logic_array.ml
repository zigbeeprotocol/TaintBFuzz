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

(* Forward references *)
let translate_rte_ref:
  (?filter:(code_annotation -> bool) -> kernel_function -> Env.t -> exp ->
   Env.t) ref =
  let func ?filter _kf _env _e =
    let _ = filter in
    Extlib.mk_labeled_fun "translate_rte_ref"
  in
  ref func

(** Retrieve the length of the [array] expression in a new variable [name] and
    return it as an expression.
    If the length is present in the type then the function directly assigns the
    length to the variable, otherwise it is computed with the formula
    [length = (\block_length(array) - \offset(array)) / sizeof(elem_typ)]. *)
let length_exp ~loc kf env ~name array =
  let elem_typ, array_len =
    match Logic_aggr.get_array_typ_opt (Cil.typeOf array) with
    | None -> Options.fatal "Trying to retrieve the length of a non-array"
    | Some (t, len, _) -> t, len
  in
  try
    let len = Cil.lenOfArray64 array_len in
    (Cil.kinteger64 ~loc len), env
  with Cil.LenOfArray _ ->
    (* check RTE on the array before accessing its block length and offset *)
    let env = !translate_rte_ref kf env array in
    (* helper function *)
    let rtl env name =
      Env.rtl_call_to_new_var
        ~loc
        env
        kf
        None
        Cil.theMachine.typeOfSizeOf
        name
        [ array ]
    in
    (* block_length(array) *)
    let block_length_exp, env = rtl env "block_length" in
    (* offset(array) *)
    let offset_exp, env = rtl env "offset" in
    (* sizeof(elem_typ) *)
    let sizeof_exp = Cil.new_exp ~loc (SizeOf elem_typ) in
    (* Create var and compute length *)
    let _, len_exp, env =
      Env.new_var
        ~loc
        env
        kf
        None
        ~name
        Cil.theMachine.typeOfSizeOf
        (fun v _ -> [
             Smart_stmt.assigns
               ~loc
               ~result:(Cil.var v)
               (Cil.mkBinOp
                  ~loc
                  Div
                  (Cil.mkBinOp ~loc MinusA block_length_exp offset_exp)
                  sizeof_exp)
           ])
    in
    len_exp, env

let comparison_to_exp ~loc kf env ~name bop array1 array2 =
  (match bop with
   | Eq | Ne -> () (* Ok *)
   | _ ->
     Options.fatal ~current:true "Something else than comparison of equality\
                                  between two arrays.");

  (* The generated code can be the same for [Ne] and [Eq] if we just adjust the
     values for the result.
     [res_value()] returns the initial value for
     the result and [res_flip_value()] returns the flipped value of the result.
     If the arrays have been coerced in ACSL to a different array size, then we
     add a check to see if the coerced size is lesser or equal to then actual
     length of the array.
     The generated code returned by this function is equivalent to:
        int result = res_value();
        size_t len1 = length(array1);
        size_t len2 = length(array2);
        if (len1 == len2) {
            // Here we add check that the coerced length doesn't exceed the
            // actual length of the arrays.
            // Then we compare the content of the arrays, using the coerced
            // length.
            for (int i = 0 ; i < len1 ; ++i) {
                if (array1[i] != array2[i]) {
                    result = res_value(flip);
                    break;
                }
            }
        } else {
            result = res_value(flip);
        }
        result
  *)
  let res_value ?(flip=false) () =
    match flip, bop with
    | false, Eq | true,  Ne -> Cil.one ~loc
    | true,  Eq | false, Ne -> Cil.zero ~loc
    | _ -> assert false
  in

  (* Helper function: call [Env.pop_and_get] with [global_clear] and [where]
     pre-set *)
  let pop_and_get_env env stmt =
    Env.pop_and_get
      env
      stmt
      ~global_clear:false
      Env.Middle
  in

  (* Create var that will hold the result of the comparison between the
     two arrays *)
  let comparison_vi, comparison_exp, env =
    Env.new_var
      ~loc
      env
      kf
      None
      ~name
      Cil.intType
      (fun v _ -> [ Smart_stmt.assigns ~loc ~result:(Cil.var v) (res_value ()) ])
  in

  (* Retrieve the length of the arrays *)
  let len1_exp, env = length_exp ~loc kf env ~name:"length1" array1 in
  let len2_exp, env = length_exp ~loc kf env ~name:"length2" array2 in

  (* Push a new env to declare the variable that will hold the iterator of the
     loop *)
  let env = Env.push env in
  let iter, iter_e, env =
    Env.new_var
      ~loc
      env
      kf
      None
      ~name:"iter"
      Cil.theMachine.typeOfSizeOf
      (fun _ _ -> [])
  in

  (* Push a new env to do the innermost comparison between two elements of the
     arrays. This env will enable us to also check RTEs *)
  let env = Env.push env in
  (* Create the access to the arrays *)
  let array1_iter_e = Smart_exp.subscript ~loc array1 iter_e in
  let array2_iter_e = Smart_exp.subscript ~loc array2 iter_e in
  (* Check RTE on the arrays, filtering out bounding checks since the accesses
     are built already in bounds *)
  let filter a =
    let index_bound =
      Alarms.get_name (Index_out_of_bound (iter_e, Some len1_exp))
    in
    match a.annot_content with
    | AAssert (_, { tp_statement = { pred_name = hd :: _ }})
      when Datatype.String.equal hd index_bound -> false
    | _ -> true
  in
  let env = !translate_rte_ref ~filter kf env array1_iter_e in
  let env = !translate_rte_ref ~filter kf env array2_iter_e in
  (* Create the condition *)
  let cond = Cil.mkBinOp ~loc Ne array1_iter_e array2_iter_e in
  (* Create the statement representing the body of the for loop *)
  let body =
    Smart_stmt.if_stmt
      ~loc
      ~cond
      (Cil.mkBlock [
          Smart_stmt.assigns ~loc ~result:(Cil.var comparison_vi) (res_value ~flip:true ());
          Smart_stmt.break ~loc
        ])
  in
  (* Pop the env to build the body of the for loop *)
  let body_blk, env = pop_and_get_env env body in

  (* Create the statement representing the full for loop *)
  let for_loop =
    (Smart_stmt.block_stmt
       (Cil.mkBlock
          (Cil.mkForIncr
             ~iter
             ~first:(Cil.zero ~loc)
             ~stopat:len1_exp
             ~incr:(Cil.one ~loc)
             ~body:[ Smart_stmt.block_stmt body_blk ]
             ()
          )
       )
    )
  in

  (* Create the list of statements that will be in the `then` block of the
     top-level if *)
  let then_stmts = [ for_loop ] in

  (* Add the check for the length before the for loop *)
  let prepend_coercion_check ~name env stmts array len =
    let array_orig = Option.get (Misc.extract_uncoerced_lval array) in
    if array_orig == array then
      stmts, env
    else
      let len_orig, env =
        length_exp ~loc kf env ~name:(name ^ "_orig") array_orig
      in
      let e = Cil.mkBinOp ~loc Le len len_orig in
      let p =
        Logic_const.prel
          ~loc
          (Rle, Logic_utils.expr_to_term len, Logic_utils.expr_to_term len_orig)
      in
      let p = { p with pred_name = "array_coercion" :: p.pred_name } in
      Typing.preprocess_predicate (Env.Local_vars.get env) p;
      let adata, env = Assert.empty ~loc kf env in
      let adata, env =
        Assert.register ~loc env "destination length" len adata
      in
      let adata, env =
        Assert.register ~loc env "current length" len_orig adata
      in
      let stmt, env =
        Assert.runtime_check ~adata ~pred_kind:Assert RTE kf env e p
      in
      stmt :: stmts, env
  in
  let then_stmts, env =
    prepend_coercion_check ~name:"length2" env then_stmts array2 len2_exp
  in
  let then_stmts, env =
    prepend_coercion_check ~name:"length1" env then_stmts array1 len1_exp
  in

  (* Pop the env to build the full then block *)
  let then_blk, env =
    pop_and_get_env env (Smart_stmt.block_stmt (Cil.mkBlock then_stmts))
  in

  (* Create the statement representing the whole generated code *)
  let stmt =
    Smart_stmt.if_stmt
      ~loc
      ~cond:(Cil.mkBinOp ~loc Eq len1_exp len2_exp)
      then_blk
      ~else_blk:(Cil.mkBlock
                   [ Smart_stmt.assigns
                       ~loc
                       ~result:(Cil.var comparison_vi)
                       (res_value ~flip:true ()) ])
  in
  (* Build the statement in the current env *)
  let env = Env.add_stmt env stmt in

  (* Return the result expression with the result of the comparison *)
  comparison_exp, env
