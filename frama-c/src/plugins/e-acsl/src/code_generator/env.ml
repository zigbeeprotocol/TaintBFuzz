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
open Analyses_types
open Contract_types
module Error = Translation_error

type localized_scope =
  | LGlobal
  | LFunction of kernel_function
  | LLocal_block of kernel_function

type mp_tbl = {
  new_exps: (varinfo * exp) Term.Map.t;
  (* generated mp variables as exp from terms *)
  clear_stmts: stmt list;
  (* stmts freeing the memory before exiting the block *)
}

type block_info = {
  new_block_vars: varinfo list;
  (* generated variables local to the block *)
  new_stmts: stmt list;
  (* generated stmts to put at the beginning of the block *)
  pre_stmts: stmt list;
  (* stmts already inserted into the current stmt,
     but which should be before [new_stmts]. *)
  post_stmts: stmt list;
}

type local_env = {
  block_info: block_info;
  mp_tbl: mp_tbl;
  rte: bool
}

type loop_env = {
  variant: (term * logic_info option) option;
  invariants: toplevel_predicate list;
}

type t = {
  lscope: Lscope.t;
  lscope_reset: bool;
  annotation_kind: annotation_kind;
  new_global_vars: (varinfo * localized_scope) list;
  (* generated variables. The scope indicates the level where the variable
     should be added. *)
  global_mp_tbl: mp_tbl;
  env_stack: local_env list;
  contract_stack: contract list;
  (* Stack of contracts for active functions and statements *)
  var_mapping: Varinfo.t Stack.t Logic_var.Map.t;
  (* records of C bindings for logic vars *)
  loop_envs: loop_env list;
  (* list of loop environment for each currently visited loops *)
  cpt: int;
  (* counter used when generating variables *)
  local_vars: Typing.Function_params_ty.t list;
  (* type of variables used in calls to logic functions and predicates *)
  kinstr: kinstr;
  (* Current kinstr of the environment *)
}

let empty_block =
  { new_block_vars = [];
    new_stmts = [];
    pre_stmts = [];
    post_stmts = [] }

let empty_mp_tbl =
  { new_exps = Term.Map.empty;
    clear_stmts = [] }

let empty_local_env =
  { block_info = empty_block;
    mp_tbl = empty_mp_tbl;
    rte = true }

let empty_loop_env =
  { variant = None;
    invariants = [] }
let empty =
  { lscope = Lscope.empty;
    lscope_reset = true;
    annotation_kind = Assertion;
    new_global_vars = [];
    global_mp_tbl = empty_mp_tbl;
    env_stack = [];
    contract_stack = [];
    var_mapping = Logic_var.Map.empty;
    loop_envs = [];
    cpt = 0;
    local_vars = [];
    kinstr = Kglobal }

let top env = match env.env_stack with
  | [] -> Options.fatal "Empty environment. That is unexpected."
  | hd :: tl -> hd, tl

let has_no_new_stmt env =
  let local, _ = top env in
  local.block_info = empty_block

(* ************************************************************************** *)
(** {2 Loop invariants} *)
(* ************************************************************************** *)

let push_loop env =
  { env with loop_envs = empty_loop_env :: env.loop_envs }

let top_loop_env env =
  match env.loop_envs with
  | [] -> assert false
  | loop_env :: tl -> loop_env, tl

let set_loop_variant ?measure env t =
  let loop_env, tl = top_loop_env env in
  let loop_env = { loop_env with variant = Some (t, measure) } in
  { env with loop_envs = loop_env :: tl }

let add_loop_invariant env inv =
  match env.loop_envs with
  | [] -> assert false
  | loop_env :: tl ->
    let loop_env = { loop_env with invariants = inv :: loop_env.invariants} in
    { env with loop_envs = loop_env :: tl }

let top_loop_variant env =
  let loop_env, _ = top_loop_env env in
  loop_env.variant

let top_loop_invariants env =
  let loop_env, _ = top_loop_env env in
  loop_env.invariants

let pop_loop env =
  let _, tl = top_loop_env env in
  { env with loop_envs = tl }

(* ************************************************************************** *)
(** {2 RTEs} *)
(* ************************************************************************** *)

let set_rte env b =
  let local_env, tl_env = top env in
  { env with env_stack = { local_env with rte = b } :: tl_env }

let generate_rte env =
  let local_env, _ = top env in
  local_env.rte

(* ************************************************************************** *)
(** {2 Kinstr} *)
(* ************************************************************************** *)

let set_kinstr env kinstr =
  { env with kinstr = kinstr }

let get_kinstr env =
  env.kinstr

(* ************************************************************************** *)

(* eta-expansion required for typing generalisation *)
let acc_list_rev acc l = List.fold_left (fun acc x -> x :: acc) acc l

let do_new_var ~loc ?(scope=Varname.Block) ?(name="") env kf t ty mk_stmts =
  let local_env, tl_env = top env in
  let local_block = local_env.block_info in
  let is_z_t = Gmp_types.Z.is_t ty in
  if is_z_t then Gmp_types.Z.is_now_referenced ();
  let is_q_t = Gmp_types.Q.is_t ty in
  if is_q_t then Gmp_types.Q.is_now_referenced ();
  let n = succ env.cpt in
  let v =
    Cil.makeVarinfo
      ~source:true
      false (* is a global? *)
      false (* is a formal? *)
      ~referenced:true
      (Varname.get ~scope (Functions.RTL.mk_gen_name name))
      ty
  in
  v.vreferenced <- true;
  let lscope = match scope with
    | Varname.Global -> LGlobal
    | Varname.Function -> LFunction kf
    | Varname.Block -> LLocal_block kf
  in
  (*  Options.feedback "new variable %a (global? %b)" Varinfo.pretty v global;*)
  let e = Cil.evar v in
  let stmts = mk_stmts v e in
  let new_stmts = acc_list_rev local_block.new_stmts stmts in
  let new_block_vars = match scope with
    | Varname.Global | Varname.Function -> local_block.new_block_vars
    | Varname.Block -> v :: local_block.new_block_vars
  in
  let new_block =
    { new_block_vars = new_block_vars;
      new_stmts = new_stmts;
      pre_stmts = local_block.pre_stmts;
      post_stmts = local_block.post_stmts
    }
  in
  v,
  e,
  if is_z_t || is_q_t then begin
    let extend_tbl tbl =
      (*      Options.feedback "memoizing %a for term %a"
              Varinfo.pretty v (fun fmt t -> match t with None -> Format.fprintf fmt
              "NONE" | Some t -> Term.pretty fmt t) t;*)
      { clear_stmts = Gmp.clear ~loc e :: tbl.clear_stmts;
        new_exps = match t with
          | None -> tbl.new_exps
          | Some t -> Term.Map.add t (v, e) tbl.new_exps }
    in
    match scope with
    | Varname.Global | Varname.Function ->
      let local_env = { local_env with block_info = new_block } in
      (* also memoize the new variable, but must never be used *)
      { env with
        cpt = n;
        new_global_vars = (v, lscope) :: env.new_global_vars;
        global_mp_tbl = extend_tbl env.global_mp_tbl;
        env_stack = local_env :: tl_env }
    | Varname.Block ->
      let local_env =
        { local_env with
          block_info = new_block;
          mp_tbl = extend_tbl local_env.mp_tbl }
      in
      { env with
        cpt = n;
        env_stack = local_env :: tl_env;
        new_global_vars = (v, lscope) :: env.new_global_vars }
  end else
    let new_global_vars = (v, lscope) :: env.new_global_vars in
    let local_env =
      { local_env with
        block_info = new_block }
    in
    { env with
      new_global_vars = new_global_vars;
      cpt = n;
      env_stack = local_env :: tl_env }

exception No_term

let new_var ~loc ?(scope=Varname.Block) ?name env kf t ty mk_stmts =
  let local_env, _ = top env in
  let memo tbl =
    try
      match t with
      | None -> raise No_term
      | Some t ->
        let v, e = Term.Map.find t tbl.new_exps in
        if Typ.equal ty v.vtype then v, e, env else raise No_term
    with Not_found | No_term ->
      do_new_var ~loc ~scope ?name env kf t ty mk_stmts
  in
  match scope with
  | Varname.Global | Varname.Function -> memo env.global_mp_tbl
  | Varname.Block -> memo local_env.mp_tbl

let new_var_and_mpz_init ~loc ?scope ?name env kf t mk_stmts =
  new_var
    ~loc
    ?scope
    ?name
    env
    kf
    t
    (Gmp_types.Z.t ())
    (fun v e -> Gmp.init ~loc e :: mk_stmts v e)

let rtl_call_to_new_var ~loc ?scope ?name env kf t ty func_name args =
  let _, exp, env =
    new_var
      ~loc
      ?scope
      ?name
      env
      kf
      t
      ty
      (fun v _ ->
         [ Smart_stmt.rtl_call ~loc ~result:(Cil.var v) func_name args ])
  in
  exp, env

module Logic_binding = struct

  let add_binding env logic_v vi =
    try
      let varinfos = Logic_var.Map.find logic_v env.var_mapping in
      Stack.push vi varinfos;
      env
    with Not_found | Stack.Empty ->
      let varinfos = Stack.create () in
      Stack.push vi varinfos;
      let var_mapping = Logic_var.Map.add logic_v varinfos env.var_mapping in
      { env with var_mapping = var_mapping }

  let add ?ty env kf logic_v =
    let ty = match ty with
      | Some ty -> ty
      | None -> match logic_v.lv_type with
        | Ctype ty -> ty
        | Linteger -> Gmp_types.Z.t ()
        | Ltype _ as ty when Logic_const.is_boolean_type ty -> Cil.charType
        | Ltype _ | Lvar _ | Lreal | Larrow _ as lty ->
          let msg =
            Format.asprintf
              "logic variable of type %a" Logic_type.pretty lty
          in
          Error.not_yet msg
    in
    let v, e, env =
      new_var
        ~loc:Location.unknown
        env
        kf
        ~name:logic_v.lv_name
        None
        ty
        (fun _ _ -> [])
    in
    v, e, add_binding env logic_v v

  let get env logic_v =
    try
      let varinfos = Logic_var.Map.find logic_v env.var_mapping in
      Stack.top varinfos
    with
    | Not_found ->
      Options.fatal
        "Unable to find logic var '%a' in environment mappings"
        Printer.pp_logic_var logic_v
    | Stack.Empty ->
      Options.fatal
        "Empty mapping stack for logic var '%a' in environment"
        Printer.pp_logic_var logic_v

  let remove env logic_v =
    try
      let varinfos = Logic_var.Map.find logic_v env.var_mapping in
      ignore (Stack.pop varinfos)
    with Not_found | Stack.Empty ->
      assert false

end

module Logic_scope = struct
  let get env = env.lscope
  let extend env lvs = { env with lscope = Lscope.add lvs env.lscope }
  let remove env lvs = { env with lscope = Lscope.remove lvs env.lscope }
  let set_reset env bool = { env with lscope_reset = bool }
  let get_reset env = env.lscope_reset
  let reset env =
    if env.lscope_reset then { env with lscope = Lscope.empty }
    else env
end

let add_assert kf stmt annot =
  Annotations.add_assert Options.emitter ~kf stmt annot

let add_stmt ?(post=false) env stmt =
  let local_env, tl = top env in
  let block = local_env.block_info in
  let block =
    if post then
      { block with post_stmts = stmt :: block.post_stmts }
    else
      { block with new_stmts = stmt :: block.new_stmts }
  in
  let local_env = { local_env with block_info = block } in
  { env with env_stack = local_env :: tl }

let extend_stmt_in_place env stmt ~label block =
  let stmt = Labels.get_first_inner_stmt stmt in
  let new_stmt = Smart_stmt.block_stmt block in
  let sk = stmt.skind in
  stmt.skind <- Block (Cil.mkBlock [ new_stmt; Smart_stmt.stmt sk ]);
  let pre = match label with
    | BuiltinLabel(Here | Post) -> true
    | BuiltinLabel(Old | Pre | LoopEntry | LoopCurrent | Init)
    | FormalLabel _ | StmtLabel _ -> false
  in
  if pre then
    let local_env, tl_env = top env in
    let b_info = local_env.block_info in
    let b_info = { b_info with pre_stmts = new_stmt :: b_info.pre_stmts } in
    { env with env_stack = { local_env with block_info = b_info } :: tl_env }
  else
    env

let push env =
  (*  Options.feedback "push (was %d)" (List.length env.env_stack);*)
  { env with env_stack = empty_local_env :: env.env_stack }

let pop env =
  (*  Options.feedback "pop";*)
  let _, tl = top env in
  { env with env_stack = tl }

let transfer ~from env = match from.env_stack, env.env_stack with
  | { block_info = from_blk } :: _, ({ block_info = env_blk } as local) :: tl
    ->
    let new_blk =
      { new_block_vars = from_blk.new_block_vars @ env_blk.new_block_vars;
        new_stmts = from_blk.new_stmts @ env_blk.new_stmts;
        pre_stmts = from_blk.pre_stmts @ env_blk.pre_stmts;
        post_stmts = from_blk.post_stmts @ env_blk.post_stmts }
    in
    { env with env_stack = { local with block_info = new_blk } :: tl }
  | _, _ ->
    assert false

type where = Before | Middle | After
let pop_and_get ?(split=false) env stmt ~global_clear where =
  let split = split && stmt.labels = [] in
  (* Options.feedback "pop_and_get from %a (%b)" Printer.pp_stmt stmt split; *)
  let local_env, tl = top env in
  let clear =
    if global_clear then begin
      Varname.clear_locals ();
      env.global_mp_tbl.clear_stmts @ local_env.mp_tbl.clear_stmts
    end else
      local_env.mp_tbl.clear_stmts
  in
  (*  Options.feedback "clearing %d mpz (global_clear: %b)"
      (List.length clear) global_clear;*)
  let block = local_env.block_info in
  let b =
    let pre_stmts, stmt =
      let rec extract stmt acc = function
        | [] -> acc, stmt
        | _ :: tl ->
          match stmt.skind with
          | Block { bstmts = [ fst; snd ] } -> extract snd (fst :: acc) tl
          | _ ->
            Kernel.fatal
              "experting a block containing 2 statements instead of %a"
              Printer.pp_stmt stmt
      in
      extract stmt [] block.pre_stmts
    in
    let new_s = block.new_stmts in
    let cat stmt l = match stmt.skind with
      | Instr(Skip _) -> l
      | _ -> stmt :: l
    in
    let stmts =
      match where with
      | Before -> cat stmt (acc_list_rev (List.rev clear) new_s)
      | Middle -> acc_list_rev (cat stmt (List.rev clear)) new_s
      | After ->
        (* if [split], do not put the given [stmt] in the generated block *)
        let stmts = if split then [] else cat stmt [] in
        acc_list_rev (acc_list_rev stmts clear) new_s
    in
    Cil.mkBlock (acc_list_rev stmts pre_stmts)
  in
  b.blocals <- acc_list_rev b.blocals block.new_block_vars;
  let b =
    (* blocks with local cannot be transient (see doc in cil.ml),
       while transient blocks prevent the E-ACSL labeling strategy from working
       properly: no transient block in that cases. *)
    if b.blocals = [] && stmt.labels = [] then Cil.transient_block b
    else b
  in
  let final_blk =
    (* if [split], put the generated code in a distinct sub-block and
       add the given [stmt] afterwards. This way, we have the guarantee that
       the final block does not contain any local, so may be transient. *)
    if split then
      let sblock = Smart_stmt.block_stmt b in
      Cil.transient_block (Cil.mkBlock [ sblock; stmt ])
    else
      b
  in
  (* remove superfluous brackets inside the generated block *)
  let final_blk = Cil.flatten_transient_sub_blocks final_blk in
  (* remove the non-scoping mark of the outermost block *)
  let final_blk = Cil.block_of_transient final_blk in
  (* add post-block statements *)
  final_blk.bstmts <- final_blk.bstmts @ block.post_stmts;
  final_blk, { env with env_stack = tl }

let get_generated_variables env = List.rev env.new_global_vars

let annotation_kind env = env.annotation_kind
let set_annotation_kind env k = { env with annotation_kind = k }

module Context = struct

  let ctx = ref []
  let save env = ctx := env.new_global_vars
  let restore env =
    if !ctx <> [] then begin
      let vars = env.new_global_vars in
      let env =
        { env with
          new_global_vars =
            List.filter
              (fun (v, scope) ->
                 (match scope with
                  | LGlobal | LFunction _ -> true
                  | LLocal_block _kf -> false)
                 && List.for_all (fun (v', _) -> v != v') vars)
              !ctx
            @ vars }
      in
      ctx := [];
      env
    end else
      env

end

module Local_vars = struct

  let push_new env =
    {env with local_vars = [] :: env.local_vars}

  let add env ty =
    match env.local_vars with
    | curr::stacked -> {env with local_vars = (ty :: curr) :: stacked}
    | [] -> Options.fatal
              "Trying to add local variable in a non-existing environment"

  let get env =
    match env.local_vars with
    | lenv :: _ -> lenv
    | [] -> []

end

let handle_error f env =
  let env = Error.handle f env in
  Context.restore env

let handle_error_with_args f (env, args) =
  let env, args = Error.handle f (env, args) in
  let env = Context.restore env in
  env, args

let not_yet env s =
  Context.save env;
  Error.not_yet s

let push_contract env contract =
  { env with contract_stack = contract :: env.contract_stack }

let top_contract env =
  match env.contract_stack with
  | [] -> Options.fatal "Contract list is empty in env. That is unexpected"
  | hd :: tl -> hd, tl

let pop_and_get_contract env =
  let hd, tl = top_contract env in
  hd, { env with contract_stack = tl }

(* ************************************************************************** *)
(** {2 Utilities} *)
(* ************************************************************************** *)

let with_params_and_result ?rte ?kinstr ~f env =
  let old_rte, env =
    match rte with
    | Some rte ->
      Some (generate_rte env), set_rte env rte
    | None -> None, env
  in
  let old_kinstr, env =
    match kinstr with
    | Some kinstr ->
      Some (get_kinstr env), set_kinstr env kinstr
    | None -> None, env
  in
  let other, env = f env in
  let env =
    match old_kinstr with
    | Some kinstr -> set_kinstr env kinstr
    | None -> env
  in
  let env =
    match old_rte with
    | Some rte -> set_rte env rte
    | None -> env
  in
  other, env

let with_params ?rte ?kinstr ~f env =
  let (), env =
    with_params_and_result ?rte ?kinstr ~f:(fun env -> (), f env) env
  in
  env

(* debugging purpose *)
let pretty fmt env =
  let local_env, _ = top env in
  Format.fprintf fmt "local new_stmts %t"
    (fun fmt ->
       List.iter
         (fun s -> Printer.pp_stmt fmt s)
         local_env.block_info.new_stmts)

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
