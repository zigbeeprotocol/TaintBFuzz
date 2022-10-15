(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(* --- Automata Helpers                                                   --- *)
(* -------------------------------------------------------------------------- *)

module WpLog = Wp_parameters
module Kf = Kernel_function
module Cfg = Interpreted_automata
module G = Cfg.G
module V = Cfg.Vertex
module Vhash = V.Hashtbl
type vertex = Cfg.vertex
type assigns = WpPropId.assigns_full_info

(* -------------------------------------------------------------------------- *)
(* --- Calculus Modes (passes)                                            --- *)
(* -------------------------------------------------------------------------- *)

type mode = {
  kf: kernel_function;
  bhv : funbehavior ;
  infos : CfgInfos.t ;
}

type props = [ `All | `Names of string list | `PropId of Property.t ]

let default_requires mode kf =
  if Cil.is_default_behavior mode.bhv then [] else
    try
      let bhv = List.find Cil.is_default_behavior (Annotations.behaviors kf) in
      CfgAnnot.get_requires ~goal:false kf bhv
    with Not_found -> []

(* -------------------------------------------------------------------------- *)
(* --- Property Selection by Mode                                         --- *)
(* -------------------------------------------------------------------------- *)

let is_default_bhv (m: mode) = Cil.is_default_behavior m.bhv

let is_selected_bhv (m: mode) (bhv: funbehavior) =
  m.bhv.b_name = bhv.b_name

let is_selected_for (m: mode) ~goal (fors: string list) =
  (fors=[] && (not goal || is_default_bhv m)) ||
  List.mem m.bhv.b_name fors

let is_selected_ca (m: mode) ~goal (ca: code_annotation) =
  match ca.annot_content with
  | AAssigns(forb,_)
  | AAllocation(forb,_)
  | AAssert(forb,_)
  | AInvariant(forb,_,_)
    -> is_selected_for m ~goal forb
  | AVariant _ -> is_default_bhv m
  | AExtended _ | AStmtSpec _ | APragma _ ->
    assert false (* n/a *)

let is_active_mode ~mode ~goal (p: Property.t) =
  let open Property in
  match p with
  | IPCodeAnnot { ica_ca } -> is_selected_ca mode ~goal ica_ca
  | IPPredicate { ip_kind } ->
    begin match ip_kind with
      | PKRequires _ | PKAssumes _ -> true
      | PKEnsures(bhv,_) -> is_selected_bhv mode bhv
      | PKTerminates -> is_default_bhv mode
    end
  | IPAllocation { ial_bhv = bhv } | IPAssigns { ias_bhv = bhv } ->
    begin match bhv with
      | Id_loop ca -> is_selected_ca mode ~goal ca
      | Id_contract(_,bhv) -> is_selected_bhv mode bhv
    end
  | IPDecrease { id_ca = None } -> is_default_bhv mode
  | IPDecrease { id_ca = Some ca } -> is_selected_ca mode ~goal ca
  | IPComplete _ | IPDisjoint _ -> is_default_bhv mode
  | IPOther _ -> true
  | IPFrom _ | IPGlobalInvariant _ | IPTypeInvariant _
  | IPAxiomatic _ | IPLemma _
  | IPExtended _ | IPBehavior _
  | IPReachable _ | IPPropertyInstance _
    -> assert false (* n/a *)

let is_selected_props (props : props) ?pi pid =
  WpPropId.filter_status pid &&
  match props with
  | `All | `Names [] -> WpPropId.select_default pid
  | `Names ps -> WpPropId.select_by_name ps pid
  | `PropId p ->
    Property.equal p @@ match pi with
    | Some q -> q
    | None -> WpPropId.property_of_id pid

let rec factorize ~wdefault = function
  | (_,w)::wcs when w==wdefault -> factorize ~wdefault wcs
  | (e,w)::wcs -> collect ~wdefault [e] w wcs
  | [] -> []
and collect ~wdefault rs wr = function
  | (e,w)::wcs when w==wr -> collect ~wdefault (e::rs) wr wcs
  | wcs -> (List.rev rs,wr) :: factorize ~wdefault wcs

(* -------------------------------------------------------------------------- *)
(* --- WP Calculus Driver from Interpreted Automata                       --- *)
(* -------------------------------------------------------------------------- *)

module Make(W : Mcfg.S) =
struct

  module I = CfgInit.Make(W)

  (* --- Traversal Environment --- *)

  type env = {
    mode: mode;
    props: props;
    body: Cfg.automaton option;
    succ: Cfg.vertex -> Cfg.G.edge list;
    dead: stmt -> bool ;
    terminates: WpPropId.pred_info option ;
    decreases: WpPropId.variant_info option ;
    we: W.t_env;
    wp: W.t_prop option Vhash.t; (* None is used for non-dag detection *)
    mutable wk: W.t_prop; (* end point *)
  }

  exception NonNaturalLoop of location

  (* --- Annotation Helpers --- *)

  let fmerge env f = function
    | [] -> W.empty
    | [x] -> f x
    | x::xs ->
      let cup = W.merge env.we in
      List.fold_left (fun p y -> cup (f y) p) (f x) xs

  let is_selected ~goal { mode ; props } (pid,_) =
    let pi = WpPropId.property_of_id pid in
    is_active_mode ~mode ~goal pi &&
    ( not goal || is_selected_props props ~pi pid )

  let is_selected_callpre { props } (pid,_) =
    is_selected_props props pid

  let use_assigns env (a : assigns) w =
    match a with
    | NoAssignsInfo -> assert false
    | AssignsAny ad ->
      WpLog.warning ~current:true ~once:true
        "Missing assigns clause (assigns 'everything' instead)" ;
      W.use_assigns env.we None ad w
    | AssignsLocations(ap,ad) -> W.use_assigns env.we (Some ap) ad w

  let prove_assigns env (a : assigns) w =
    match a with
    | NoAssignsInfo | AssignsAny _ -> w
    | AssignsLocations ai ->
      if is_selected ~goal:true env ai
      then W.add_assigns env.we ai w
      else w

  let use_property ?for_pid env (p : WpPropId.pred_info) w =
    if is_selected ~goal:false env p then W.add_hyp ?for_pid env.we p w else w

  let prove_property env (p : WpPropId.pred_info) w =
    if is_selected ~goal:true env p then W.add_goal env.we p w else w

  let prove_subproperty env p ?deps prop stmt source w =
    if is_selected ~goal:true env p
    then W.add_subgoal env.we ?deps p prop stmt source w
    else w

  let on_selected_terminates env f =
    match env.terminates with
    | Some t when is_default_bhv env.mode && is_selected ~goal:true env t ->
      f env t
    | _ ->
      Extlib.id

  (* --- Decomposition of WP Rules --- *)

  let rec wp (env:env) (a:vertex) : W.t_prop =
    match Vhash.find env.wp a with
    | None -> raise (NonNaturalLoop (Cil.CurrentLoc.get()));
    | Some pi -> pi
    | exception Not_found ->
      (* cut circularities *)
      Vhash.add env.wp a None ;
      let pi = match a.vertex_start_of with
        | None -> successors env a
        | Some s -> stmt env a s
      in Vhash.replace env.wp a (Some pi) ; pi

  (* Compute a stmt node *)
  and stmt env a (s: stmt) : W.t_prop =
    let kl = Cil.CurrentLoc.get () in
    try
      Cil.CurrentLoc.set (Stmt.loc s) ;
      let smoking =
        is_default_bhv env.mode && env.dead s in
      let cas = CfgAnnot.get_code_assertions ~smoking env.mode.kf s in
      let opt_fold f = Option.fold ~none:Extlib.id ~some:f in
      let do_assert env CfgAnnot.{ code_admitted ; code_verified } w =
        opt_fold (prove_property env) code_verified @@
        opt_fold (use_property env) code_admitted w
      in
      let pi =
        W.label env.we (Some s) (Clabels.stmt s) @@
        List.fold_right (do_assert env) cas @@
        control env a s
      in
      Cil.CurrentLoc.set kl ; pi
    with err ->
      Cil.CurrentLoc.set kl ; raise err

  (* Branching wrt control-flow *)
  and control env a s : W.t_prop =
    match a.vertex_control with
    | If { cond ; vthen ; velse } ->
      let wthen = wp env vthen in
      let welse = wp env velse in
      W.test env.we s cond wthen welse
    | Switch { value ; cases ; default } ->
      let wcases = List.map (fun (e,v) -> e,wp env v) cases in
      let wdefault = wp env default in
      W.switch env.we s value (factorize ~wdefault wcases) wdefault
    | Loop _ ->
      let m = env.mode in
      let smoking =
        is_default_bhv m &&
        WpLog.SmokeTests.get () &&
        WpLog.SmokeDeadloop.get () in
      let terminates = Option.map snd env.terminates in
      loop env a s (CfgAnnot.get_loop_contract ~smoking ?terminates m.kf s)
    | Edges -> successors env a

  (* Compute loops *)
  and loop env a s (lc : CfgAnnot.loop_contract) : W.t_prop =
    let insert_terminates w = match env.terminates, lc.loop_terminates with
      | None, _ | _, None -> w (* no terminates goal or nothing to prove *)
      | Some t, Some prop -> prove_subproperty env t prop s FromCode w
    in
    let prove_invariant env pid pred w =
      match pid with None -> w | Some pid -> prove_property env (pid, pred) w
    in
    let assume_invariant env (hyp: CfgAnnot.loop_hypothesis) pred ind w =
      match hyp with
      | NoHyp -> w
      | Check pid -> use_property ?for_pid:ind env (pid, pred) w
      | Always pid -> use_property env (pid, pred) w
    in
    let established env CfgAnnot.{ loop_hyp; loop_ind; loop_est; loop_pred } w =
      prove_invariant env loop_est loop_pred @@
      assume_invariant env loop_hyp loop_pred loop_ind w
    in
    let loop_current_hyp env CfgAnnot.{ loop_hyp ; loop_ind ; loop_pred } w =
      assume_invariant env loop_hyp loop_pred loop_ind w
    in
    let preserved env CfgAnnot.{ loop_hyp ; loop_ind ; loop_pred } w =
      prove_invariant env loop_ind loop_pred @@
      begin match loop_hyp with
        | CfgAnnot.Always pid -> use_property env (pid, loop_pred)
        | _ -> Extlib.id (* we never assume this one for checks *)
      end w
    in
    insert_terminates @@
    List.fold_right (established env) lc.loop_invariants @@
    List.fold_right (use_assigns env) lc.loop_assigns @@
    W.label env.we None (Clabels.loop_current s) @@
    List.fold_right (loop_current_hyp env) lc.loop_invariants @@
    List.fold_right (prove_property env) lc.loop_smoke @@
    let q =
      List.fold_right (preserved env) lc.loop_invariants @@
      List.fold_right (prove_assigns env) lc.loop_assigns @@
      W.empty in
    ( Vhash.replace env.wp a (Some q) ; successors env a )

  (* Merge transitions *)
  and successors env (a : vertex) = transitions env (env.succ a)
  and transitions env (es : G.edge list) = fmerge env (transition env) es
  and transition env (_,edge,dst) : W.t_prop =
    let p = wp env dst in
    match edge.edge_transition with
    | Skip -> p
    | Return(r,s) -> W.return env.we s r p
    | Enter { blocals=[] } | Leave { blocals=[] } -> p
    | Enter { blocals=xs } -> W.scope env.we xs SC_Block_in p
    | Leave { blocals=xs } -> W.scope env.we xs SC_Block_out p
    | Instr (i,s) -> instr env s i p
    | Prop _ | Guard _ -> (* soundly ignored *) p

  (* Compute a single instruction *)
  and instr env s instr (w : W.t_prop) : W.t_prop =
    match instr with
    | Skip _ | Code_annot _ -> w
    | Set(lv,e,_) -> W.assign env.we s lv e w
    | Local_init(x,AssignInit i,_) -> W.init env.we x (Some i) w
    | Local_init(x,ConsInit (vf, args, kind), loc) ->
      Cil.treat_constructor_as_func
        begin fun r fct args _loc ->
          match Kf.get_called fct with
          | Some kf -> call env s r kf args w
          | None ->
            WpLog.warning ~once:true "No function for constructor '%s'"
              vf.vname ;
            let any = WpPropId.mk_stmt_assigns_any_desc s in
            W.use_assigns env.we None any (W.merge env.we w env.wk)
        end x vf args kind loc
    | Call(res,fct,args,_loc) ->
      begin
        match Kf.get_called fct with
        | Some kf -> call env s res kf args w
        | None ->
          match Dyncall.get ~bhv:env.mode.bhv.b_name s with
          | None ->
            WpLog.warning ~once:true "Missing 'calls' for %s"
              (if Cil.is_default_behavior env.mode.bhv
               then "default behavior"
               else env.mode.bhv.b_name) ;
            let any = WpPropId.mk_stmt_assigns_any_desc s in
            W.use_assigns env.we None any (W.merge env.we w env.wk)
          | Some(prop,kfs) ->
            let id = WpPropId.mk_property prop in
            W.call_dynamic env.we s id fct @@
            List.map (fun kf -> kf, call env s res kf args w) kfs
      end
    | Asm _ ->
      let assigns = CfgAnnot.get_stmt_assigns env.mode.kf s in
      List.fold_right (use_assigns env) assigns w

  and call env s r kf es wr : W.t_prop =
    let smoking =
      if is_default_bhv env.mode &&
         WpLog.SmokeTests.get () &&
         WpLog.SmokeDeadcall.get ()
      then Some s else None in
    let c = CfgAnnot.get_call_contract ?smoking kf s in
    let p_post = List.fold_right (prove_property env) c.contract_smoke wr in
    let p_exit = List.fold_right (prove_property env) c.contract_smoke env.wk in
    let w_call = W.call env.we s r kf es
        ~pre:c.contract_hpre
        ~post:c.contract_post
        ~pexit:c.contract_exit
        ~assigns:c.contract_assigns
        ~p_post ~p_exit in
    let w_pre = if is_default_bhv env.mode then
        let pre = List.filter (is_selected_callpre env) c.contract_cond in
        W.call_goal_precond env.we s kf es ~pre w_call
      else w_call
    in
    let callee_t =
      (* TODO when kernel terminates complete: remove this code. *)
      let generated, callee_t = c.contract_terminates in
      if generated && env.terminates <> None then
        Wp_parameters.warning ~once:true
          "Missing terminates clause on call to %a, defaults to %a"
          Kernel_function.pretty kf Cil_printer.pp_predicate callee_t ;
      Some callee_t
    in
    let selected t = is_selected ~goal:true env t && is_default_bhv env.mode in
    let in_cluster = CfgInfos.in_cluster ~caller:env.mode.kf kf in
    let w_term = match env.terminates with
      | Some t when selected t ->
        W.call_terminates env.we s kf es t ?callee_t w_pre
      | _ -> w_pre
    in
    let w_decr = match env.decreases with
      | Some d when selected d && in_cluster ->
        W.call_decreases env.we s kf es d
          ?caller_t:(Option.map snd env.terminates)
          ?callee_d:c.contract_decreases
          w_term
      | _ -> w_term
    in
    w_decr

  let do_complete_disjoint env w =
    if not (is_default_bhv env.mode) then w
    else
      let kf = env.mode.kf in
      let complete = CfgAnnot.get_complete_behaviors kf in
      let disjoint = CfgAnnot.get_disjoint_behaviors kf in
      List.fold_right (prove_property env) complete @@
      List.fold_right (prove_property env) disjoint w

  let do_terminates_deps env w =
    match env.body with
    | None -> w
    | Some _ ->
      let deps = CfgInfos.terminates_deps env.mode.infos in
      let return = Kernel_function.find_return env.mode.kf in
      let prove goal env t w =
        prove_subproperty env t ~deps goal return FromReturn w
      in
      if CfgInfos.is_recursive env.mode.kf then
        (* there is a dependency on terminates or decreases is missing *)
        let goal =
          if None <> env.decreases then Logic_const.ptrue
          else begin
            WpLog.warning ~once:true
              "No 'decreases' clause on recursive function '%a', \
               cannot prove termination"
              Kernel_function.pretty env.mode.kf ;
            Logic_const.pfalse
          end
        in
        on_selected_terminates env (prove goal) w
      else
      if not @@ Property.Set.is_empty deps then
        on_selected_terminates env (prove Logic_const.ptrue) w
      else w

  let do_global_init env w =
    I.process_global_init env.we env.mode.kf @@
    W.scope env.we [] SC_Global w

  let do_preconditions env ~formals (b : CfgAnnot.behavior) w =
    let kf = env.mode.kf in
    let init = Globals.is_entry_point ~when_lib_entry:false kf in
    let side_behaviors =
      if init || WpLog.PrecondWeakening.get () then []
      else CfgAnnot.get_preconditions ~goal:false kf in
    let requires_init = if init then b.bhv_requires else [] in
    (* pre-state *)
    W.label env.we None Clabels.pre @@
    (* pre-conditions *)
    List.fold_right (use_property env) (default_requires env.mode kf) @@
    List.fold_right (use_property env) b.bhv_assumes @@
    List.fold_right (prove_property env) requires_init @@
    List.fold_right (use_property env) b.bhv_requires @@
    List.fold_right (prove_property env) b.bhv_smokes @@
    List.fold_right (use_property env) side_behaviors @@
    (* frame-in *)
    W.scope env.we formals SC_Frame_in w

  let do_post env ~formals (b : CfgAnnot.behavior) w =
    W.label env.we None Clabels.post @@
    W.scope env.we formals SC_Frame_out @@
    List.fold_right (prove_property env) b.bhv_ensures @@
    prove_assigns env b.bhv_post_assigns w

  let do_exit env ~formals (b : CfgAnnot.behavior) w =
    W.label env.we None Clabels.exit @@
    W.scope env.we formals SC_Frame_out @@
    List.fold_right (prove_property env) b.bhv_exits @@
    prove_assigns env b.bhv_exit_assigns w

  let do_funbehavior env ~formals ~exits (b:CfgAnnot.behavior) w =
    match env.body with
    | None -> w
    | Some cfg ->
      let wpost = do_post env ~formals b w in
      Vhash.add env.wp cfg.return_point (Some wpost) ;
      env.wk <- if exits then do_exit env ~formals b w else w ;
      wp env cfg.entry_point

  (* Putting everything together *)
  let compute ~mode ~props =
    let kf = mode.kf in
    let infos = mode.infos in
    let body = CfgInfos.body infos in
    let succ = match body with
      | None -> (fun _ -> [])
      | Some cfg -> Cfg.G.succ_e cfg.graph in
    let dead =
      if body <> None &&
         is_default_bhv mode &&
         WpLog.SmokeTests.get () &&
         WpLog.SmokeDeadcode.get ()
      then CfgInfos.smoking infos else (fun _ -> false) in
    let terminates = CfgAnnot.get_terminates_goal kf in
    let decreases = CfgAnnot.get_decreases_goal kf in
    let env = {
      mode ; props ; body ;
      succ ; dead ; terminates ; decreases ;
      we = W.new_env kf ;
      wp = Vhash.create 32 ;
      wk = W.empty ;
    } in
    let formals = Kf.get_formals kf in
    let exits = not @@ Kf.Set.is_empty @@ CfgInfos.calls infos in
    let smoking = WpLog.SmokeTests.get () in
    let bhv = CfgAnnot.get_behavior_goals kf ~smoking ~exits mode.bhv in
    begin
      W.close env.we @@
      do_terminates_deps env @@
      do_global_init env @@
      do_preconditions env ~formals bhv @@
      do_complete_disjoint env @@
      do_funbehavior env ~formals ~exits bhv @@
      W.empty
    end

end

(* -------------------------------------------------------------------------- *)
