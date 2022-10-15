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
open Contract_types
module Error = Translation_error

(**************************************************************************)
(********************** Contract ********************************)
(**************************************************************************)

type t = contract

(** Module to ease the access to the C API for contracts *)
module Rtl_call: sig
  val init:
    loc:location -> result_name:string -> Env.t -> kernel_function -> int ->
    varinfo * exp * Env.t
  (** Call the C function [__e_acsl_contract_init] *)

  val cleanup:
    loc:location -> Env.t -> exp -> Env.t
  (** Call the C function [__e_acsl_contract_cleanup] *)

  val set_assumes:
    loc:location -> Env.t -> kernel_function -> exp -> int -> predicate ->
    Env.t
  (** Call the C function [__e_acsl_contract_set_behavior_assumes] *)

  val get_assumes:
    loc:location -> result:varinfo -> Env.t -> exp -> int -> Env.t
  (** Call the C function [__e_acsl_contract_get_behavior_assumes] *)

  val partial_count_behaviors:
    loc:location -> result:varinfo -> Env.t -> exp -> int list -> Env.t
  (** Call the C function [__e_acsl_contract_partial_count_behaviors] *)

  val partial_count_all_behaviors:
    loc:location -> result:varinfo -> Env.t -> exp -> Env.t
    (** Call the C function [__e_acsl_contract_partial_count_all_behaviors] *)

end = struct
  let init_function_name = "contract_init"

  let ctyp_lazy =
    lazy
      (Globals.Types.find_type
         Logic_typing.Typedef (Functions.RTL.mk_api_name "contract_t"))

  let init ~loc ~result_name env kf count =
    (* Add a call to init in the environment *)
    let ty = TPtr(Lazy.force ctyp_lazy, []) in
    Env.new_var
      ~loc
      ~name:result_name
      ~scope:Varname.Function
      env
      kf
      None
      ty
      (fun vi _e ->
         let result = Cil.var vi in
         let count_e = Cil.integer ~loc count in
         [ Smart_stmt.rtl_call
             ~loc
             ~result
             init_function_name
             [count_e] ])

  let cleanup ~loc env contract =
    Env.add_stmt
      env
      (Smart_stmt.rtl_call
         ~loc
         "contract_clean"
         [contract])

  let set_assumes ~loc env kf contract idx assumes =
    let idx_e = Cil.integer ~loc idx in
    let assumes_e, _, env =
      Translate_predicates.generalized_untyped_to_exp
        ~adata:Assert.no_data
        kf
        env
        assumes
    in
    Env.add_stmt
      env
      (Smart_stmt.rtl_call
         ~loc
         "contract_set_behavior_assumes"
         [contract; idx_e; assumes_e])

  let get_assumes ~loc ~result env contract idx =
    let idx_e = Cil.integer ~loc idx in
    let result = Cil.var result in
    Env.add_stmt
      env
      (Smart_stmt.rtl_call
         ~loc
         ~result
         "contract_get_behavior_assumes"
         [contract; idx_e])

  let partial_count_behaviors ~loc ~result env contract idxes =
    let idxes, count =
      List.fold_right
        (fun idx (idxes, count) ->
           Cil.integer ~loc idx :: idxes, count + 1)
        idxes
        ([], 0)
    in
    let result = Cil.var result in
    Env.add_stmt
      env
      (Smart_stmt.rtl_call
         ~loc
         ~result
         "contract_partial_count_behaviors"
         (contract :: Cil.integer ~loc count :: idxes))

  let partial_count_all_behaviors ~loc ~result env contract =
    let result = Cil.var result in
    Env.add_stmt
      env
      (Smart_stmt.rtl_call
         ~loc
         ~result
         "contract_partial_count_all_behaviors"
         [ contract ])
end

(** Convert the given assumes clauses list to a single [predicate] *)
let assumes_predicate env assumes =
  let p =
    List.fold_left
      (fun acc p ->
         let pred = p.ip_content.tp_statement in
         let loc = pred.pred_loc in
         Logic_const.pand ~loc
           (acc,
            Logic_const.unamed ~loc pred.pred_content))
      Logic_const.ptrue
      assumes
  in
  Typing.preprocess_predicate (Env.Local_vars.get env) p;
  p

let create ~loc spec =
  (* Create a hashtable to associate a behavior name with an index *)
  let name_to_idx_tbl = Hashtbl.create 7 in
  let named_behaviors_count =
    List.fold_left
      (fun idx b ->
         if Cil.is_default_behavior b then
           idx
         else begin
           Hashtbl.add name_to_idx_tbl b.b_name idx;
           idx + 1
         end
      )
      0
      spec.spec_behavior
  in
  let var = None in
  (* Create the contract *)
  { location = loc;
    named_behaviors_count;
    name_to_idx_tbl;
    var;
    all_assumes_translated = true;
    spec }

(** Initialize the C API for the given contract *)
let init kf env contract =
  if contract.named_behaviors_count > 0 then
    let loc = contract.location in
    let contract_vi, contract_e, env =
      Rtl_call.init
        ~loc
        ~result_name:"contract"
        env
        kf
        contract.named_behaviors_count
    in
    contract.var <- Some (contract_vi, contract_e);
    env
  else env

(** Cleanup the C API for the given contract *)
let cleanup env contract =
  match contract.var with
  | None -> env
  | Some (_, e) ->
    let loc = contract.location in
    Rtl_call.cleanup ~loc env e

(** Retrieve the behavior index from its name for the given contract *)
let get_bhvr_idx contract bhvr_name =
  (* by construction, the behavior name is in the hashtable *)
  try Hashtbl.find contract.name_to_idx_tbl bhvr_name
  with _ -> assert false

(** Retrieve the C variable with the contract structure for the given contract.
    Assumes that there is such a variable. *)
let get_contract_var contract =
  match contract.var with
  | Some (contract_vi, contract_e) -> contract_vi, contract_e
  | None ->
    Options.fatal
      "Unexpected call to get_contract_var with a contract without named \
       behaviors"

(** Setup the assumes values for the C API *)
let setup_assumes kf env contract =
  match contract.var with
  | None -> env
  | Some (_, contract_e) ->
    let do_fold env b =
      let do_it env =
        try
          if Cil.is_default_behavior b then
            env
          else
            let assumes = assumes_predicate env b.b_assumes in
            let loc = assumes.pred_loc in
            Cil.CurrentLoc.set loc;
            let idx = get_bhvr_idx contract b.b_name in
            Rtl_call.set_assumes ~loc env kf contract_e idx assumes
        with exn ->
          (* Unable to translate the assumes clause. Save that fact and re-raise
             the exception *)
          contract.all_assumes_translated <- false;
          raise exn
      in
      Env.handle_error do_it env
    in
    List.fold_left do_fold env contract.spec.spec_behavior

(** Returns a closure that will (1) creates a local C variable when first
    called and (2) returns said variable on subsequent calls. *)
let mk_get_or_create_var kf typ var_name =
  let var_ref = ref None in
  let f ~loc env =
    match !var_ref with
    | None ->
      let vi, e, env =
        Env.new_var
          ~loc
          ~scope:Varname.Block
          ~name:var_name
          env
          kf
          None
          typ
          (fun _ _ -> [])
      in
      var_ref := Some (vi, e);
      vi, e, env
    | Some (vi, e) -> vi, e, env
  in
  f

(** Drop-in replacement for [List.fold_left] with the folding function wrapped
    in a [handle_error] call *)
let fold_left_handle_error f env l =
  (* Reverse input args of f *)
  let f2 x env = f env x in
  (* Call fold_left on the list with handle_error at each element *)
  List.fold_left
    (fun env x ->
       Env.handle_error (f2 x) env)
    env
    l

(** Drop-in replacement for [List.fold_left] when the accumulator is more than
    the [env], with the folding function wrapped in a [handle_error] call.

    The accumulator for the fold should be set up with a pair where the first
    element is the environment and the second element the rest of the
    accumulator. *)
let fold_left_handle_error_with_args f (env, acc) l =
  let f2 x (env, args) = f (env, args) x in
  List.fold_left
    (fun (env, args) x ->
       Env.handle_error_with_args (f2 x) (env, args))
    (env, acc)
    l

(** Insert requires check for the default behavior of the given contract in the
    environment. *)
let check_default_requires kf env contract =
  let kinstr = Env.get_kinstr env in
  let default_behavior =
    Cil.find_default_behavior contract.spec
  in
  match default_behavior with
  | Some b ->
    fold_left_handle_error
      (fun env ip_requires ->
         if Translate_utils.must_translate
             (Property.ip_of_requires kf kinstr b ip_requires) then
           let tp_requires = ip_requires.ip_content in
           let loc = tp_requires.tp_statement.pred_loc in
           Cil.CurrentLoc.set loc;
           Translate_predicates.do_it kf env tp_requires
         else
           env)
      env
      b.b_requires
  | None -> env

(** Insert requires check for the behaviors other than the default behavior of
    the given contract in the environment *)
let check_other_requires kf env contract =
  let get_or_create_assumes_var =
    mk_get_or_create_var kf Cil.intType "assumes_value"
  in
  let kinstr = Env.get_kinstr env in
  let do_behavior env b =
    if Cil.is_default_behavior b then
      env
    else
      (* Compute the assumes predicate for pretty-printing *)
      let assumes = assumes_predicate env b.b_assumes in
      (* Push a new env and check the requires of the behavior *)
      let env = Env.push env in
      let env, stmts =
        fold_left_handle_error_with_args
          (fun (env, stmts) ip_requires ->
             if Translate_utils.must_translate
                 (Property.ip_of_requires kf kinstr b ip_requires) then
               let tp_requires = ip_requires.ip_content in
               let pred_kind = tp_requires.tp_kind in
               match pred_kind with
               | Assert | Check ->
                 let requires = tp_requires.tp_statement in
                 let loc = requires.pred_loc in
                 Cil.CurrentLoc.set loc;
                 (* Prepend the name of the behavior *)
                 let requires =
                   { requires with pred_name = b.b_name :: requires.pred_name }
                 in
                 Typing.preprocess_predicate (Env.Local_vars.get env) requires;
                 (* Create runtime check *)
                 let adata, env = Assert.empty ~loc kf env in
                 let requires_e, adata, env =
                   Translate_predicates.generalized_untyped_to_exp
                     ~adata
                     kf
                     env
                     requires
                 in
                 let stmt, env =
                   Assert.runtime_check
                     ~adata
                     ~pred_kind
                     Precondition
                     kf
                     env
                     requires_e
                     requires
                 in
                 env, stmt :: stmts
               | Admit -> env, stmts
             else
               env, stmts)
          (env, [])
          b.b_requires
      in
      let requires = Smart_stmt.block_from_stmts stmts in
      (* Pop the env to build the requires check *)
      let requires_blk, env =
        Env.pop_and_get
          env
          requires
          ~global_clear:false
          Env.Middle
      in
      match stmts with
      | [] ->
        (* If no requires check have been generated, then return immediately *)
        env
      | _ :: _ ->
        (* Generate a predicate that will retrieve and test the
           already computed assumes value for the behavior *)
        let loc = assumes.pred_loc in
        Cil.CurrentLoc.set loc;
        let assumes_vi, assumes_e, env =
          get_or_create_assumes_var ~loc env
        in
        let _, contract_e = get_contract_var contract in
        let idx = get_bhvr_idx contract b.b_name in
        let env =
          Rtl_call.get_assumes
            ~loc
            ~result:assumes_vi
            env
            contract_e
            idx
        in
        let stmt = Smart_stmt.if_stmt ~loc ~cond:assumes_e requires_blk in
        Env.add_stmt env stmt
  in
  List.fold_left
    do_behavior
    env
    contract.spec.spec_behavior

type translate_ppt =
  | Complete
  | Disjoint
  | Both

(** For each set of behavior names in [clauses], [check_active_behaviors] counts
    the number of active behaviors and creates assertions for the
    [ppt_to_translate]. *)
let check_active_behaviors ~ppt_to_translate ~get_or_create_var kf env contract clauses =
  let kinstr = Env.get_kinstr env in
  let loc = contract.location in
  Cil.CurrentLoc.set loc;
  let do_clause env bhvrs =
    let bhvrs_list = Datatype.String.Set.elements bhvrs in
    let active = [] in (* TODO: 'for' behaviors, e-acsl#109 *)
    let must_translate_complete =
      match ppt_to_translate with
      | Both | Complete ->
        Translate_utils.must_translate
          (Property.ip_of_complete kf kinstr ~active bhvrs_list)
      | Disjoint -> false
    in
    let must_translate_disjoint =
      match ppt_to_translate with
      | Both | Disjoint ->
        Translate_utils.must_translate
          (Property.ip_of_disjoint kf kinstr ~active bhvrs_list)
      | Complete -> false
    in

    if must_translate_complete || must_translate_disjoint then
      (* Retrieve the number of active behaviors *)
      let active_bhvrs_e, complete_msg, disjoint_msg, env =
        let _, contract_e = get_contract_var contract in
        let vi, e, env = get_or_create_var ~loc env in
        let clause_card = Datatype.String.Set.cardinal bhvrs in
        let env, complete_msg, disjoint_msg =
          if Datatype.Int.equal clause_card contract.named_behaviors_count then
            let env =
              Rtl_call.partial_count_all_behaviors
                ~loc
                ~result:vi
                env
                contract_e
            in
            let complete_msg = "all behaviors complete" in
            let disjoint_msg = "all behaviors disjoint" in
            env, complete_msg, disjoint_msg
          else
            let args, bhvrs_names =
              Datatype.String.Set.fold
                (fun bhvr_name (args, bhvrs_names) ->
                   let args = get_bhvr_idx contract bhvr_name :: args in
                   let bhvrs_names = bhvr_name :: bhvrs_names in
                   args, bhvrs_names)
                bhvrs
                ([], [])
            in
            let env =
              Rtl_call.partial_count_behaviors
                ~loc
                ~result:vi
                env
                contract_e
                args
            in
            let bhvrs_names = String.concat ", " bhvrs_names in
            let complete_msg =
              Format.sprintf "complete behaviors %s" bhvrs_names
            in
            let disjoint_msg =
              Format.sprintf "disjoint behaviors %s" bhvrs_names
            in
            env, complete_msg, disjoint_msg
        in
        e, complete_msg, disjoint_msg, env
      in

      (* Create assertions for complete and disjoint behaviors checks *)
      let create_assert_stmt env bop msg =
        let adata, env = Assert.empty ~loc kf env in
        let adata, env =
          Assert.register
            ~loc
            env
            "number of active behaviors"
            active_bhvrs_e
            adata
        in
        Assert.runtime_check_with_msg
          ~adata
          ~loc
          msg
          ~pred_kind:Assert
          (Env.annotation_kind env)
          kf
          env
          (Cil.mkBinOp ~loc bop active_bhvrs_e (Cil.one ~loc))
      in
      let assert_complete_stmt, env = create_assert_stmt env Ge complete_msg in
      let assert_disjoint_stmt, env = create_assert_stmt env Le disjoint_msg in

      if must_translate_complete && must_translate_disjoint then
        (* Build an enclosing [if] if both complete and disjoint must be checked
           for the given clause *)
        Env.add_stmt
          env
          (Smart_stmt.if_stmt
             ~loc
             ~cond:(Cil.mkBinOp ~loc Ne active_bhvrs_e (Cil.one ~loc))
             (Cil.mkBlock [ assert_complete_stmt; assert_disjoint_stmt ]))
          (* Otherwise just get the corresponding assertion *)
      else if must_translate_complete then
        Env.add_stmt env assert_complete_stmt
      else if must_translate_disjoint then
        Env.add_stmt env assert_disjoint_stmt
      else
        (* By construction, at least either [must_translate_complete] or
           [must_translate_disjoint] is true *)
        assert false
    else
      (* Nothing to translate *)
      env
  in
  fold_left_handle_error do_clause env clauses

(** Insert complete and disjoint behaviors check for the given contract in the
    environement *)
let check_complete_and_disjoint kf env contract =
  (* Only translate the complete and disjoint clauses if all the assumes clauses
     could be translated *)
  if contract.all_assumes_translated then
    (* Partition the complete and disjoint clauses of the contract into 3 lists:
       - The complete and disjoint list
       - The complete list
       - The disjoint list

       The behaviors of a clause are stored in a Set so that they are
       automatically sorted, the duplicates are removed, and they can be
       compared for equality.
    *)
    let completes =
      List.map
        Datatype.String.Set.of_list
        contract.spec.spec_complete_behaviors
    in
    let completes_and_disjoints, completes, disjoints =
      List.fold_left
        (fun (completes_and_disjoints, completes, disjoints) clause ->
           let clause = Datatype.String.Set.of_list clause in
           if List.mem clause completes then
             let completes_and_disjoints = clause :: completes_and_disjoints in
             let completes =
               List.filter
                 (fun c -> not (Datatype.String.Set.equal clause c))
                 completes
             in
             completes_and_disjoints, completes, disjoints
           else
             let disjoints = clause :: disjoints in
             completes_and_disjoints, completes, disjoints
        )
        ([], completes, [])
        contract.spec.spec_disjoint_behaviors
    in
    (* Create a common variable to hold the number of active behavior for the
       current check *)
    let get_or_create_var =
      mk_get_or_create_var kf Cil.intType "active_bhvrs"
    in
    (* Check the complete and disjoint clauses *)
    let check_bhvrs env ppt_to_translate bhvrs =
      check_active_behaviors
        ~ppt_to_translate
        ~get_or_create_var
        kf
        env
        contract
        bhvrs
    in
    let env = check_bhvrs env Both completes_and_disjoints in
    let env = check_bhvrs env Complete completes in
    let env = check_bhvrs env Disjoint disjoints in
    env
  else begin
    Cil.CurrentLoc.set contract.location;
    Options.warning
      ~current:true
      "@[Some assumes clauses could not be translated.@ Ignoring complete and \
       disjoint behaviors annotations.@]";
    env
  end

(** Insert ensures check for the given contract in the environement *)
let check_post_conds kf env contract =
  let get_or_create_assumes_var =
    mk_get_or_create_var kf Cil.intType "assumes_value"
  in
  let kinstr = Env.get_kinstr env in
  let do_behavior env b =
    let env =
      Env.handle_error
        (fun env ->
           let active = [] in (* TODO: 'for' behaviors, e-acsl#109 *)
           let ppt = Property.ip_assigns_of_behavior kf kinstr ~active b in
           if b.b_assigns <> WritesAny && Translate_utils.must_translate_opt ppt
           then Env.not_yet env "assigns clause in behavior";
           (* ignore b.b_extended since we never translate them *)
           env)
        env
    in
    if Cil.is_default_behavior b then
      fold_left_handle_error
        (fun env ((termination, ip_post_cond) as tp) ->
           if Translate_utils.must_translate
               (Property.ip_of_ensures kf kinstr b tp) then
             let tp_post_cond = ip_post_cond.ip_content in
             let loc = tp_post_cond.tp_statement.pred_loc in
             Cil.CurrentLoc.set loc;
             match termination with
             | Normal ->
               (* If translating the default behavior, directly translate the
                  predicate *)
               Translate_predicates.do_it kf env tp_post_cond
             | Exits | Breaks | Continues | Returns ->
               Error.print_not_yet "abnormal termination case in behavior";
               env
           else
             env)
        env
        b.b_post_cond
    else
      (* Compute the assumes predicate for pretty printing *)
      let assumes = assumes_predicate env b.b_assumes in
      (* Push a new env and check the ensures of the behavior *)
      let env = Env.push env in
      let env, stmts =
        fold_left_handle_error_with_args
          (fun (env, stmts) ((termination, ip_post_cond) as tp) ->
             if Translate_utils.must_translate
                 (Property.ip_of_ensures kf kinstr b tp) then
               let tp_post_cond = ip_post_cond.ip_content in
               let pred_kind = tp_post_cond.tp_kind in
               match pred_kind with
               | Assert | Check -> begin
                   let post_cond = tp_post_cond.tp_statement in
                   let loc = post_cond.pred_loc in
                   Cil.CurrentLoc.set loc;
                   match termination with
                   | Normal ->
                     (* Prepend the name of the behavior *)
                     let post_cond =
                       { post_cond with
                         pred_name = b.b_name :: post_cond.pred_name }
                     in
                     Typing.preprocess_predicate
                       (Env.Local_vars.get env)
                       post_cond;
                     (* Create runtime check *)
                     let adata, env = Assert.empty ~loc kf env in
                     let post_cond_e, adata, env =
                       Translate_predicates.generalized_untyped_to_exp
                         ~adata
                         kf
                         env
                         post_cond
                     in
                     let stmt, env =
                       Assert.runtime_check
                         ~adata
                         ~pred_kind
                         Postcondition
                         kf
                         env
                         post_cond_e
                         post_cond
                     in
                     env, stmt :: stmts
                   | Exits | Breaks | Continues | Returns ->
                     Error.print_not_yet
                       "abnormal termination case in behavior";
                     env, stmts
                 end
               | Admit -> env, stmts
             else
               env, stmts)
          (env, [])
          b.b_post_cond
      in
      let post_cond = Smart_stmt.block_from_stmts stmts in
      (* Pop the env to build the post_cond check *)
      let post_cond_blk, env =
        Env.pop_and_get
          env
          post_cond
          ~global_clear:false
          Env.Middle
      in
      match stmts with
      | [] ->
        (* If no post_cond check have been generated, then return immediately *)
        env
      | _ :: _ ->
        (* Generate a predicate that retrieves and tests the already
           computed assumes value for the behavior *)
        let loc = assumes.pred_loc in
        let assumes_vi, assumes_e, env =
          get_or_create_assumes_var ~loc env
        in
        let _, contract_e = get_contract_var contract in
        let idx = get_bhvr_idx contract b.b_name in
        let env =
          Rtl_call.get_assumes
            ~loc
            ~result:assumes_vi
            env
            contract_e
            idx
        in
        let stmt = Smart_stmt.if_stmt ~loc ~cond:assumes_e post_cond_blk in
        Env.add_stmt env stmt
  in
  List.fold_left
    do_behavior
    env
    contract.spec.spec_behavior

let translate_preconditions kf env contract =
  let env = Env.set_annotation_kind env Precondition in
  let env = Env.push_contract env contract in
  let env = init kf env contract in
  (* Start with translating the requires predicate of the default behavior. *)
  let env =
    Env.handle_error
      (fun env -> check_default_requires kf env contract)
      env
  in
  (* Then setup the assumes clauses of the contract. *)
  let env = setup_assumes kf env contract in
  (* And finally translate the requires predicates of the rest of the behaviors,
     skipping over the default behavior. *)
  let do_it env =
    let env = check_other_requires kf env contract in
    let env = check_complete_and_disjoint kf env contract in
    env
  in
  Env.handle_error do_it env

let translate_postconditions kf env =
  let env = Env.set_annotation_kind env Postcondition in
  let contract, env = Env.pop_and_get_contract env in
  let do_it env =
    let env = check_post_conds kf env contract in
    env
  in
  let env = Env.handle_error do_it env in
  cleanup env contract
