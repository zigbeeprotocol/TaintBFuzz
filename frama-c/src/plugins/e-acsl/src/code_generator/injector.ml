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

let dkey = Options.Dkey.translation

(* ************************************************************************** *)
(* Expressions *)
(* ************************************************************************** *)

let replace_literal_string_in_exp env kf_opt (* None for globals *) e =
  (* do not touch global initializers because they accept only constants;
     replace literal strings elsewhere *)
  match kf_opt with
  | None -> e, env
  | Some kf -> Literal_observer.subst_all_literals_in_exp env kf e

let replace_literal_strings_in_args env kf_opt (* None for globals *) args =
  List.fold_right
    (fun a (args, env) ->
       let a, env = replace_literal_string_in_exp env kf_opt a in
       a :: args, env)
    args
    ([], env)

(* rewrite names of functions for which we have alternative definitions in the
   RTL. *)
let rename_caller ~loc caller args =
  if Options.Replace_libc_functions.get ()
  && Functions.Libc.has_replacement caller.vorig_name then begin
    (* rewrite names of functions for which we have alternative definitions in
       the RTL. *)
    let fvi =
      Rtl.Symbols.replacement
        ~get_name:Functions.Libc.replacement_name
        caller
    in
    fvi, args
  end
  else if Functions.Concurrency.has_replacement caller.vorig_name then
    if Options.Concurrency.get () then
      let fvi =
        Rtl.Symbols.replacement
          ~get_name:Functions.Concurrency.replacement_name
          caller
      in
      fvi, args
    else begin
      Memory_tracking.found_concurrent_function ~loc caller;
      caller, args
    end
  else if Options.Validate_format_strings.get ()
       && Functions.Libc.is_printf_name caller.vorig_name then
    (* rewrite names of format functions (such as printf). This case differs
       from the above because argument list of format functions is extended with
       an argument describing actual variadic arguments *)
    (* replacement name, e.g., [printf] -> [__e_acsl_builtin_printf] *)
    let fvi =
      Rtl.Symbols.replacement
        ~get_name:Functions.Libc.replacement_name
        caller
    in
    let fmt =
      Functions.Libc.get_printf_argument_str ~loc caller.vorig_name args
    in
    fvi, fmt :: args
  else
    caller, args

let rec inject_in_init env kf_opt vi off = function
  | SingleInit e as init ->
    if vi.vglob then Global_observer.add_initializer vi off init;
    let e, env = replace_literal_string_in_exp env kf_opt e in
    SingleInit e, env
  | CompoundInit(typ, l) ->
    (* inject in all single initializers that can be built from the compound
       version *)
    let l, env =
      List.fold_left
        (fun (l, env) (off', i) ->
           let new_off = Cil.addOffset off' off in
           let i, env = inject_in_init env kf_opt vi new_off i in
           (off', i) :: l, env)
        ([], env)
        l
    in
    CompoundInit(typ, List.rev l), env

let inject_in_local_init ~loc env kf vi = function
  | ConsInit (fvi, sz :: _, _) as init
    when Functions.Libc.is_vla_alloc_name fvi.vname ->
    (* add a store statement when creating a variable length array *)
    let store = Smart_stmt.store_stmt ~str_size:sz vi in
    let env = Env.add_stmt ~post:true env store in
    init, env

  | ConsInit (caller, args, kind) ->
    let args, env = replace_literal_strings_in_args env (Some kf) args in
    let caller, args = rename_caller ~loc caller args in
    let _, env =
      if Libc.is_writing_memory caller then begin
        let result = Var vi, NoOffset in
        Libc.update_memory_model ~loc env kf ~result caller args
      end else
        None, env
    in
    ConsInit(caller, args, kind), env

  | AssignInit init ->
    let init, env = inject_in_init env (Some kf) vi NoOffset init in
    AssignInit init, env

(* ************************************************************************** *)
(* Instructions and statements *)
(* ************************************************************************** *)

(* TODO: should be better documented *)
let add_initializer loc ?vi lv ?(post=false) stmt env kf =
  if Functions.instrument kf then
    let may_safely_ignore = function
      | Var vi, NoOffset -> vi.vglob || vi.vformal
      | _ -> false
    in
    let must_model = Memory_tracking.must_monitor_lval ~stmt ~kf lv in
    if not (may_safely_ignore lv) && must_model then
      let new_stmt =
        (* bitfields are not yet supported ==> no initializer.
           a [not_yet] will be raised in [Translate]. *)
        if Cil.isBitfield lv then Cil.mkEmptyStmt ()
        else Smart_stmt.initialize ~loc lv
      in
      let env = Env.add_stmt ~post env new_stmt in
      let env = match vi with
        | None -> env
        | Some vi ->
          let new_stmt = Smart_stmt.store_stmt vi in
          Env.add_stmt ~post env new_stmt
      in
      env
    else
      env
  else
    env

let inject_in_instr env kf stmt = function
  | Set(lv, e, loc) ->
    let e, env = replace_literal_string_in_exp env (Some kf) e in
    let env = add_initializer loc lv stmt env kf in
    Set(lv, e, loc), env

  | Call(result, caller, args, loc) ->
    let args, env = replace_literal_strings_in_args env (Some kf) args in
    let caller, args =
      match caller.enode with
      | Lval (Var fvi, _) ->
        let fvi, args = rename_caller ~loc fvi args in
        Cil.evar fvi, args
      | _ -> caller, args
    in
    (* if this is a call to a libc function that writes into a memory block then
       manually update the memory model *)
    let result, env =
      match caller.enode with
      | Lval (Var cvi, _) when Libc.is_writing_memory cvi ->
        Libc.update_memory_model ~loc env kf ?result cvi args
      | _ -> result, env
    in
    (* add statement tracking initialization of return values *)
    let env =
      match result with
      | Some lv when not (Functions.RTL.is_generated_kf kf) ->
        add_initializer loc lv ~post:false stmt env kf
      | _ ->
        env
    in
    (* if this is a call to free a vla, add a call to delete_block *)
    let env =
      if Functions.Libc.is_vla_free caller then
        match args with
        | [ { enode = CastE (_, { enode = Lval (Var vi, NoOffset) }) } ] ->
          let delete_block = Smart_stmt.delete_stmt ~is_addr:true vi in
          Env.add_stmt env delete_block
        | _ -> Options.fatal "The normalization of __fc_vla_free() has changed"
      else
        env
    in
    Call(result, caller, args, loc), env

  | Local_init(vi, linit, loc) ->
    let lv = Var vi, NoOffset in
    let env = add_initializer loc ~vi lv ~post:true stmt env kf in
    let linit, env = inject_in_local_init ~loc env kf vi linit in
    Local_init(vi, linit, loc), env

  (* nothing to do: *)
  | Asm _
  | Skip _
  | Code_annot _ as instr ->
    instr, env

let add_new_block_in_stmt env kf stmt =
  (* Add temporal analysis instrumentations *)
  let env = Temporal.handle_stmt stmt env kf in
  let new_stmt, env =
    if Functions.check kf then
      let env =
        (* handle ghost statement *)
        if stmt.ghost then begin
          stmt.ghost <- false;
          (* translate potential RTEs of ghost code *)
          let rtes = Rte.stmt ~warn:false kf stmt in
          List.iter
            (Typing.preprocess_rte ~lenv:(Env.Local_vars.get env))
            rtes;
          Translate_rtes.rte_annots Printer.pp_stmt stmt kf env rtes
        end else
          env
      in
      (* handle loop annotations *)
      let new_stmt, env = Loops.handle_annotations env kf stmt in
      new_stmt, env
    else
      stmt, env
  in
  let mk_post_env env stmt =
    Annotations.fold_code_annot
      (fun _ a env -> Translate_annots.post_code_annotation kf stmt env a)
      stmt
      env
  in
  let new_stmt, env =
    (* Remove local variables which scopes ended via goto/break/continue. *)
    let del_vars = Exit_points.delete_vars stmt in
    let env = Memory_observer.delete_from_set env kf del_vars in
    if Kernel_function.is_return_stmt kf stmt then
      let env =
        if Functions.check kf then
          (* must generate the post_block before including [stmt] (the
             'return') since no code is executed after it. However, since
             this statement is pure (Cil invariant), that is semantically
             correct. *)
          (* [JS 2019/2/19] TODO: what about the other ways of early exiting
             a block? *)
          let env = mk_post_env env stmt in
          (* also handle the postcondition of the function and clear the
             env *)
          Translate_annots.post_funspec kf env
        else
          env
      in
      (* de-allocating memory previously allocating by the kf *)
      (* remove recorded function arguments *)
      let fargs = Kernel_function.get_formals kf in
      let env = Memory_observer.delete_from_list env kf fargs in
      let b, env =
        Env.pop_and_get env new_stmt ~global_clear:true Env.After
      in
      let new_stmt = Smart_stmt.block stmt b in
      new_stmt, env
    else (* i.e. not (is_return stmt) *)
      (* must generate [pre_block] which includes [stmt] before generating
         [post_block] *)
      let pre_block, env =
        Env.pop_and_get
          ~split:true
          env
          new_stmt
          ~global_clear:false
          Env.After
      in
      let env =
        (* if [kf] is not monitored, do not translate any postcondition,
           but still push an empty environment consumed by
           [Env.pop_and_get] below. This [Env.pop_and_get] call is always
           required in order to generate the code not directly related to
           the annotations of the current stmt in anycase. *)
        if Functions.check kf then mk_post_env (Env.push env) stmt
        else Env.push env
      in
      let post_block, env =
        Env.pop_and_get
          env
          (Smart_stmt.block new_stmt pre_block)
          ~global_clear:false
          Env.Before
      in
      let post_block =
        if post_block.blocals = [] && new_stmt.labels = []
        then Cil.transient_block post_block
        else post_block
      in
      let res = Smart_stmt.block new_stmt post_block in
      res, env
  in
  Options.debug ~level:4
    "@[new stmt (from sid %d):@ %a@]" stmt.sid Printer.pp_stmt new_stmt;
  new_stmt, env

(** In the block [outer_block] in the function [kf], this function finds the
    innermost last statement and insert the list of statements returned by
    [last_stmts].
    The function [last_stmts] receives an optional argument [?return_stmt] with
    the innermost return statement if it exists. In that case the function needs
    to return this statement as the last statement. *)
let insert_as_last_stmts_in_innermost_block ~last_stmts outer_block =
  (* Retrieve the last innermost block *)
  let rec retrieve_innermost_last_return block =
    let l = List.rev block.bstmts in
    match l with
    | [] -> block, [], None
    | { skind = Return _ } as ret :: rest -> block, rest, Some ret
    | { skind = Block b } :: _ -> retrieve_innermost_last_return b
    | _ :: _ -> block, l, None
  in
  let inner_block, rev_content, return_stmt =
    retrieve_innermost_last_return outer_block
  in
  (* Create the statements to insert *)
  let new_stmts = last_stmts ?return_stmt () in
  (* Move the labels from the return stmt to the stmts to insert *)
  let new_stmts =
    match return_stmt with
    | Some return_stmt ->
      let b = Cil.mkBlock new_stmts in
      let new_stmt = Smart_stmt.block return_stmt b in
      [ new_stmt ]
    | None -> new_stmts
  in
  (* Insert the statements as the last statements of the innermost block *)
  inner_block.bstmts <- List.rev_append rev_content new_stmts

(* visit the substmts and build the new skind *)
let rec inject_in_substmt env kf stmt = match stmt.skind with
  | Instr instr ->
    let instr, env = inject_in_instr env kf stmt instr in
    Instr instr, env

  | Return(Some e, loc)  ->
    let e, env = replace_literal_string_in_exp env (Some kf) e in
    Return(Some e, loc), env

  | If(e, blk1, blk2, loc) ->
    let env = inject_in_block env kf blk1 in
    let env = inject_in_block env kf blk2 in
    let e, env = replace_literal_string_in_exp env (Some kf) e in
    If(e, blk1, blk2, loc), env

  | Switch(e, blk, stmts, loc) ->
    (* [blk] and [stmts] are visited at the same time *)
    let env = inject_in_block env kf blk in
    let e, env = replace_literal_string_in_exp env (Some kf) e in
    Switch(e, blk, stmts, loc), env

  | Loop(_ (* ignore AST annotations *), blk, loc, stmt_opt1, stmt_opt2) ->
    let env = inject_in_block env kf blk in
    let do_opt env = function
      | None -> None, env
      | Some stmt ->
        let stmt, env = inject_in_stmt env kf stmt in
        Some stmt, env
    in
    let stmt_opt1, env = do_opt env stmt_opt1 in
    let stmt_opt2, env = do_opt env stmt_opt2 in
    Loop([], blk, loc, stmt_opt1, stmt_opt2), env

  | Block blk as skind ->
    skind, inject_in_block env kf blk

  | UnspecifiedSequence l ->
    let l, env =
      List.fold_left
        (fun (l, env) (stmt, l1, l2, l3, srefs) ->
           let stmt, env = inject_in_stmt env kf stmt in
           (stmt, l1, l2, l3, srefs) :: l, env)
        ([], env)
        l
    in
    UnspecifiedSequence (List.rev l), env

  | Throw(Some(e, ty), loc) ->
    let e, env = replace_literal_string_in_exp env (Some kf) e in
    Throw(Some(e, ty), loc), env

  | TryCatch(blk, l, _loc) as skind ->
    let env = inject_in_block env kf blk in
    let env =
      List.fold_left
        (fun env (cb, blk) ->
           let env = inject_in_catch_binder env kf cb in
           inject_in_block env kf blk)
        env
        l
    in
    skind, env

  | TryFinally(blk1, blk2, _loc) as skind ->
    let env = inject_in_block env kf blk1 in
    let env = inject_in_block env kf blk2 in
    skind, env

  | TryExcept(_blk1, (_instrs, _e), _blk2, _loc) ->
    Error.not_yet "try ... except ..."

  (* nothing to do: *)
  | Throw(None, _)
  | Return(None, _)
  | Goto _ (* do not visit the internal stmt since it has already been handle *)
  | Break _
  | Continue _ as skind ->
    skind, env

and inject_in_stmt env kf stmt =
  Options.debug ~level:4
    "proceeding stmt (sid %d) %a@."
    stmt.sid Stmt.pretty stmt;
  (* pushing a new context *)
  let env = Env.push env in
  let env = match stmt.skind with
    | Loop _ -> Env.push_loop env
    | _ -> env
  in
  let env = Env.set_kinstr env (Kstmt stmt) in
  (* initial environment *)
  let env, translate_pre_funspec =
    if Kernel_function.is_first_stmt kf stmt then
      let env =
        if Kernel_function.is_main kf then
          env
        else
          let env =
            Memory_observer.store env kf (Kernel_function.get_formals kf)
          in
          Temporal.handle_function_parameters kf env
      in
      (* check if the precondition of the function needs to be translated *)
      env, Functions.check kf
    else
      env, false
  in
  (* translate all \at() predicates and terms that reference the current stmt *)
  let env = Translate_ats.for_stmt env kf stmt in
  (* translate the precondition of the function *)
  let env =
    if translate_pre_funspec then
      let funspec = Annotations.funspec kf in
      Translate_annots.pre_funspec kf env funspec
    else
      env
  in
  (* translate code annotations *)
  let env =
    if Functions.check kf then
      Annotations.fold_code_annot
        (fun _ a env -> Translate_annots.pre_code_annotation kf stmt env a)
        stmt
        env
    else
      env
  in
  (* add [__e_acsl_store_duplicate] calls for local variables which declarations
     are bypassed by gotos. Note: should be done before visiting instructions
     (which adds initializers), otherwise init calls appear before store
     calls. *)
  let duplicates = Exit_points.store_vars stmt in
  let env = Memory_observer.duplicate_store env kf duplicates in
  let skind, env = inject_in_substmt env kf stmt in
  stmt.skind <- skind;
  (* building the new block of code *)
  add_new_block_in_stmt env kf stmt

and inject_in_block (env: Env.t) kf blk =
  blk.battrs <- Cil.dropAttribute Cil.frama_c_ghost_else blk.battrs ;
  let stmts, env =
    List.fold_left
      (fun (stmts, env) stmt ->
         let stmt, env = inject_in_stmt env kf stmt in
         stmt :: stmts, env)
      ([], env)
      blk.bstmts
  in
  blk.bstmts <- List.rev stmts;
  (* now inject code that de-allocates the necessary observation variables and
     blocks of the runtime memory that have been previously allocated *)
  (* calls to [free] for de-allocating variables observing \at(_,_) *)
  let free_stmts = Translate_ats.Free.find_all kf in
  match blk.blocals, free_stmts with
  | [], [] ->
    env
  | [], _ :: _ | _ :: _, [] | _ :: _, _ :: _ ->
    (* [TODO] this piece of code could be improved *)
    (* de-allocate the memory blocks observing locals *)
    let last_stmts ?return_stmt () =
      let stmts =
        match return_stmt with
        | Some return_stmt ->
          (* now that [free] stmts for [kf] have been inserted,
             there is no more need to keep the corresponding entries in the
             table managing them. *)
          Translate_ats.Free.remove_all kf;
          (* The free statements are passed in the same order than the malloc
             ones. In order to free the variable in the reverse order, the list
             is reversed before appending the return statement. Moreover,
             [List.rev_append] is tail recursive contrary to [List.append] *)
          List.rev_append free_stmts [ return_stmt ]
        | None -> []
      in
      if Functions.instrument kf then
        List.fold_left
          (fun acc vi ->
             if Memory_tracking.must_monitor_vi ~kf vi
             then Smart_stmt.delete_stmt vi :: acc
             else acc)
          stmts
          blk.blocals
      else
        stmts
    in
    (* select the precise location to inject these pieces of code *)
    insert_as_last_stmts_in_innermost_block ~last_stmts blk ;
    (* allocate the memory blocks observing locals *)
    if Functions.instrument kf then
      blk.bstmts <-
        List.fold_left
          (fun acc vi ->
             if Memory_tracking.must_monitor_vi vi && not vi.vdefined
             then Smart_stmt.store_stmt vi :: acc
             else acc)
          blk.bstmts
          blk.blocals;
    env

and inject_in_catch_binder env kf = function
  | Catch_exn(_, l) ->
    List.fold_left (fun env (_, blk) -> inject_in_block env kf blk) env l
  | Catch_all ->
    env

(* ************************************************************************** *)
(* Function definition *)
(* ************************************************************************** *)

let add_generated_variables_in_function env fundec =
  let vars = Env.get_generated_variables env in
  let locals, blocks =
    List.fold_left
      (fun (local_vars, block_vars as acc) (v, scope) -> match scope with
         (* TODO: [kf] assumed to be consistent. Should be asserted. *)
         (* TODO: actually, is the kf as constructor parameter useful? *)
         | Env.LFunction _kf -> v :: local_vars, v :: block_vars
         | Env.LLocal_block _kf -> v :: local_vars, block_vars
         | _ -> acc)
      (fundec.slocals, fundec.sbody.blocals)
      vars
  in
  fundec.slocals <- locals;
  fundec.sbody.blocals <- blocks

(* Memory management for \at on purely logic variables: put [malloc] stmts at
   proper locations *)
let add_malloc_and_free_stmts kf fundec =
  let malloc_stmts = Translate_ats.Malloc.find_all kf in
  let fstmts = malloc_stmts @ fundec.sbody.bstmts in
  fundec.sbody.bstmts <- fstmts;
  (* now that [malloc] stmts for [kf] have been inserted, there is no more need
     to keep the corresponding entries in the table managing them. *)
  Translate_ats.Malloc.remove_all kf

let inject_in_fundec main fundec =
  let vi = fundec.svar in
  let kf = try Globals.Functions.get vi with Not_found -> assert false in
  (* convert ghost variables *)
  vi.vghost <- false;
  let unghost_local vi =
    Cil.update_var_type vi (Cil.typeRemoveAttributesDeep ["ghost"] vi.vtype);
    vi.vghost <- false
  in
  List.iter unghost_local fundec.slocals;
  let unghost_formal vi =
    unghost_local vi ;
    vi.vattr <- Cil.dropAttribute Cil.frama_c_ghost_formal vi.vattr
  in
  List.iter unghost_formal fundec.sformals;
  (* update environments *)
  (* TODO: do it only for built-ins *)
  Builtins.update vi.vname vi;
  (* track function addresses but the main function that is tracked internally
     via RTL *)
  if not (Kernel_function.is_main kf) then Global_observer.add vi;
  (* exit point computations *)
  if Functions.instrument kf then Exit_points.generate fundec;
  (* recursive visit *)
  Options.feedback ~dkey ~level:2 "entering in function %a."
    Kernel_function.pretty kf;
  let env = inject_in_block Env.empty kf fundec.sbody in
  Exit_points.clear ();
  add_generated_variables_in_function env fundec;
  add_malloc_and_free_stmts kf fundec;
  (* setting main if necessary *)
  let main = if Kernel_function.is_main kf then Some kf else main in
  Options.feedback ~dkey ~level:2 "function %a done."
    Kernel_function.pretty kf;
  main

(* ************************************************************************** *)
(* The whole AST *)
(* ************************************************************************** *)

let unghost_vi vi =
  (* do not convert extern ghost variables, because they can't be linked,
     see bts #1392 *)
  if vi.vstorage <> Extern then vi.vghost <- false;
  Cil.update_var_type vi (Cil.typeRemoveAttributesDeep ["ghost"] vi.vtype);
  match Cil.unrollType vi.vtype with
  | TFun(res, Some l, va, attr) ->
    (* unghostify function's parameters *)
    let retype (n, t, a) = n, t, Cil.dropAttribute Cil.frama_c_ghost_formal a in
    Cil.update_var_type vi (TFun(res, Some (List.map retype l), va, attr))
  | _ ->
    ()

let inject_in_global main global =
  let update_builtin vi = Builtins.update vi.vname vi; main in
  let observe_and_unghost vi =
    unghost_vi vi; Global_observer.add vi; main
  in
  let var_def vi init =
    Global_observer.add vi;
    unghost_vi vi;
    let _init, _env = inject_in_init Env.empty None vi NoOffset init in
    (* ignore the new initializer that handles literal strings
           since they are not substituted in global initializers
           (see  [replace_literal_string_in_exp]) *)
    main
  in
  let fun_def ({svar = vi} as fundec) =
    unghost_vi vi;
    inject_in_fundec main fundec
  in
  E_acsl_visitor.case_globals
    ~default:(fun () -> main)
    ~builtin:update_builtin
    ~var_fun_decl:observe_and_unghost
    ~var_init:observe_and_unghost
    ~var_def
    ~fun_def
    global

(* Insert [stmt_begin] as the first statement of [fundec] and insert [stmt_end]
   as the last before [return] *)
let surround_function_with fundec stmt_begin stmt_end =
  let body = fundec.sbody in
  (* Insert last statement *)
  Option.iter
    (fun stmt_end ->
       let last_stmts ?return_stmt () =
         match return_stmt with
         | Some return_stmt -> [ stmt_end; return_stmt ]
         | None -> [ stmt_end]
       in
       insert_as_last_stmts_in_innermost_block ~last_stmts body)
    stmt_end;
  (* Insert first statement *)
  body.bstmts <- stmt_begin :: body.bstmts

(* TODO: what about using [file.globalinit]? *)
(** Add a call to [__e_acsl_globals_init] and [__e_acsl_globals_delete] if the
    memory model analysis is running.
    These functions track the usage of globals if the program being analyzed. *)
let inject_global_handler file main =
  Options.feedback ~dkey ~level:2 "building global handler.";
  if Memory_tracking.use_monitoring () then
    (* Create [__e_acsl_globals_init] function *)
    let vi_init, fundec_init = Global_observer.mk_init_function () in
    let cil_fct_init = GFun(fundec_init, Location.unknown) in
    (* Create [__e_acsl_globals_delete] function *)
    let vi_and_fundec_clean_opt = Global_observer.mk_clean_function () in
    let cil_fct_clean_opt =
      Option.map
        (fun (_, fundec_clean) -> GFun(fundec_clean, Location.unknown))
        vi_and_fundec_clean_opt
    in
    match main with
    | Some main ->
      let mk_fct_call vi =
        let exp = Cil.evar ~loc:Location.unknown vi in
        let stmt =
          Cil.mkStmtOneInstr ~valid_sid:true
            (Call(None, exp, [], Location.unknown))
        in
        vi.vreferenced <- true;
        stmt
      in
      let main_fundec =
        try Kernel_function.get_definition main
        with _ -> assert false (* by construction, the main kf has a fundec *)
      in
      (* Create [__e_acsl_globals_init();] call *)
      let stmt_init = mk_fct_call vi_init in
      (* Create [__e_acsl_globals_delete();] call *)
      let stmt_clean_opt =
        Option.map
          (fun (vi_clean, _) -> mk_fct_call vi_clean)
          vi_and_fundec_clean_opt
      in
      (* Surround the content of main with the calls to
         [__e_acsl_globals_init();] and [__e_acsl_globals_delete();] *)
      surround_function_with main_fundec stmt_init stmt_clean_opt;
      (* Retrieve all globals except main *)
      let main_vi = Globals.Functions.get_vi main in
      let new_globals =
        List.fold_left
          (fun acc g -> match g with
             | GFun({ svar = vi }, _) when Varinfo.equal vi main_vi -> acc
             | _ -> g :: acc)
          []
          file.globals
      in
      (* Add the globals functions and re-add main at the end *)
      let new_globals =
        let rec rev_and_extend acc = function
          | [] -> acc
          | f :: l -> rev_and_extend (f :: acc) l
        in
        (* [main] at the end *)
        let globals_to_add = [ GFun(main_fundec, Location.unknown) ] in
        (* Prepend [__e_acsl_globals_clean] if not empty *)
        let globals_to_add =
          Option.fold
            ~none:globals_to_add
            ~some:(fun cil_fct_clean -> cil_fct_clean :: globals_to_add)
            cil_fct_clean_opt
        in
        (* Prepend [__e_acsl_globals_init] *)
        let globals_to_add = cil_fct_init :: globals_to_add in
        (* Add these functions to the globals *)
        rev_and_extend globals_to_add new_globals
      in
      (* add the literal string varinfos as the very first globals *)
      let new_globals =
        Literal_strings.fold
          (fun _ vi l -> GVar(vi, { init = None }, Location.unknown) :: l)
          new_globals
      in
      file.globals <- new_globals
    | None ->
      Kernel.warning "@[no entry point specified:@ \
                      you must call functions `%s', `%s', \
                      `__e_acsl_memory_init' and `__e_acsl_memory_clean' \
                      by yourself.@]"
        Global_observer.function_init_name
        Global_observer.function_clean_name;
      let globals_func =
        Option.fold
          ~none:[ cil_fct_init ]
          ~some:(fun cil_fct_clean -> [ cil_fct_init; cil_fct_clean ])
          cil_fct_clean_opt
      in
      file.globals <- file.globals @ globals_func

(** Add a call to [__e_acsl_memory_init] and [__e_acsl_memory_clean] if the
    memory tracking analysis is running or if the option [assert-print-data] is
    used.
    [__e_acsl_memory_init] initializes memory storage and potentially records
    program arguments. Parameters to [__e_acsl_memory_init] are addresses of
    program arguments or NULLs if [main] is declared without arguments.
    [__e_acsl_memory_clean] clean the memory allocated by
    [__e_acsl_memory_init]. *)
let inject_mtracking_handler main =
  if Memory_tracking.use_monitoring () ||
     Options.Assert_print_data.get () then begin
    let loc = Location.unknown in
    let nulls = [ Smart_exp.null ~loc ; Smart_exp.null ~loc ] in
    let handle_main main =
      let fundec =
        try Kernel_function.get_definition main
        with _ -> assert false (* by construction, the main kf has a fundec *)
      in
      let args =
        (* record arguments only if the second has a pointer type, so argument
           strings can be recorded. This is sufficient to capture C99 compliant
           arguments and GCC extensions with environ. *)
        match fundec.sformals with
        | [] ->
          (* no arguments to main given *)
          nulls
        | _argc :: argv :: _ when Cil.isPointerType argv.vtype ->
          (* grab addresses of arguments for a call to the main initialization
             function, i.e., [__e_acsl_memory_init] *)
          List.map Cil.mkAddrOfVi fundec.sformals;
        | _ :: _ ->
          (* some non-standard arguments. *)
          nulls
      in
      let ptr_size = Cil.sizeOf ~loc Cil.voidPtrType in
      let args = args @ [ ptr_size ] in
      let init = Smart_stmt.rtl_call ~loc "memory_init" args in
      let clean = Smart_stmt.rtl_call ~loc "memory_clean" [] in
      surround_function_with fundec init (Some clean)
    in
    Option.iter handle_main main
  end

let inject_in_file file =
  let main =
    List.fold_left inject_in_global None file.globals
  in
  (* post-treatment *)
  (* extend [main] with forward initialization and put it at end *)
  if not (Global_observer.is_empty () && Literal_strings.is_empty ()) then
    inject_global_handler file main;
  file.globals <- Logic_functions.add_generated_functions file.globals;
  inject_mtracking_handler main

let reset_all ast =
  (* by default, do not run E-ACSL on the generated code *)
  Options.Run.off ();
  (* reset all the E-ACSL environments to their original states *)
  Translate_ats.reset ();
  Logic_functions.reset ();
  Global_observer.reset ();
  Analyses.reset ();
  (* reset some kernel states: *)
  (* reset the CFG that has been heavily modified by the code generation step *)
  Cfg.clearFileCFG ~clear_id:false ast;
  Cfg.computeFileCFG ast;
  (* notify the kernel that new code has been generated (but we have kept the
     old one) *)
  Ast.mark_as_grown ()

let inject () =
  let ast = Ast.get () in
  let current_project = Project.current() in
  Options.feedback ~level:2
    "injecting annotations as code in %a"
    Project.pretty current_project;
  inject_in_file ast;
  reset_all ast;

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
