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

(* -------------------------------------------------------------------------- *)
(* --- WP Calculus                                                        --- *)
(* -------------------------------------------------------------------------- *)

open LogicUsage
open Cil_types
open Cil_datatype
open WpPropId
open Clabels
open Qed
open Lang
open Lang.F
open Sigs
open Wpo

module type VCgen =
sig
  include Mcfg.S
  val register_lemma : logic_lemma -> unit
  val compile_lemma : logic_lemma -> Wpo.t
  val compile_wp : Wpo.index -> t_prop -> Wpo.t Bag.t
end

module VC( C : Sigs.Compiler ) : VCgen =
struct

  open C
  open C.M
  module V = Vars
  module P = WpPropId.PropId

  let state = Mstate.create (module M)

  type target =
    | Gprop of P.t
    | Gsource of P.t * Stmt.t * effect_source
    | Gposteffect of P.t

  module TARGET =
  struct
    type t = target
    let hsrc = function
      | FromCode -> 1 | FromCall -> 2 | FromReturn -> 3
    let hash = function
      | Gprop p | Gposteffect p -> P.hash p
      | Gsource(p,s,e) -> P.hash p * 37 + 41 * Stmt.hash s + hsrc e
    let compare g1 g2 =
      if g1 == g2 then 0 else
        match g1,g2 with
        | Gprop p1 , Gprop p2 -> P.compare p1 p2
        | Gprop _ , _ -> (-1)
        | _ , Gprop _ -> 1
        | Gsource(p1,s1,e1) , Gsource(p2,s2,e2) ->
          let c = P.compare p1 p2 in
          if c <> 0 then c else
            let c = Stmt.compare s1 s2 in
            if c <> 0 then c else
              hsrc e1 - hsrc e2
        | Gsource _ , _ -> (-1)
        | _ , Gsource _ -> 1
        | Gposteffect p1 , Gposteffect p2 -> P.compare p1 p2
    let equal g1 g2 = (compare g1 g2 = 0)
    let prop_id = function Gprop p | Gposteffect p | Gsource(p,_,_) -> p
    let source = function Gprop _ | Gposteffect _ -> None | Gsource(_,s,e) -> Some(s,e)
    let is_smoke_test = function
      | Gprop p -> WpPropId.is_smoke_test p
      | Gposteffect _ | Gsource _ -> false
    let pretty fmt = function
      | Gprop p -> WpPropId.pretty fmt p
      | Gsource(p,s,FromCode) -> Format.fprintf fmt "%a at sid:%d" WpPropId.pretty p s.sid
      | Gsource(p,s,FromCall) -> Format.fprintf fmt "Call %a at sid:%d" WpPropId.pretty p s.sid
      | Gsource(p,s,FromReturn) -> Format.fprintf fmt "Return %a at sid:%d" WpPropId.pretty p s.sid
      | Gposteffect p -> Format.fprintf fmt "%a post-effect" WpPropId.pretty p
  end

  (* Authorized written region from an assigns specification *)
  type effect = {
    e_pid : P.t ; (* Assign Property *)
    e_post : bool ; (* Requires post effects (loop-assigns or post-assigns) *)
    e_label : c_label ; (* scope for collection *)
    e_valid : L.sigma ; (* sigma where locations are filtered for validity *)
    e_region : L.region ; (* expected from spec *)
    e_warn : Warning.Set.t ; (* from translation *)
  }

  module EFFECT =
  struct
    type t = effect
    let compare e1 e2 = P.compare e1.e_pid e2.e_pid
    let pretty fmt e =
      Format.fprintf fmt "@[<hov 2>EFFECT %a:@ %a@]"
        P.pretty e.e_pid (Cvalues.pp_region M.pretty) e.e_region
    [@@ warning "-32"]
  end

  module G = Qed.Collection.Make(TARGET)
  module W = Warning.Set
  module D = Property.Set
  module S = Stmt.Set
  module Eset = Set.Make(EFFECT)
  module Gset = G.Set
  module Gmap = G.Map

  type vc = {
    hyps : Conditions.bundle ;
    goal : F.pred ;
    vars : Vars.t ; (* the variables of effects/goal to collect *)
    warn : W.t ;
    deps : D.t ;
    path : S.t ;
  }

  (* -------------------------------------------------------------------------- *)
  (* --- MCFG Interface                                                     --- *)
  (* -------------------------------------------------------------------------- *)

  type t_env = {
    frame : L.frame ;
    main : L.env ;
  }

  type t_prop = {
    sigma : L.sigma option ;
    effects : Eset.t ;
    vcs : vc Splitter.t Gmap.t ;
  }

  (* -------------------------------------------------------------------------- *)
  (* --- MCFG Pretty                                                        --- *)
  (* -------------------------------------------------------------------------- *)

  let pp_vc fmt vc =
    if Wp_parameters.debug_atleast 2 then
      begin
        List.iter
          (Format.fprintf fmt "Have @[<hov 2>%a@]@." F.pp_pred)
          (Conditions.extract vc.hyps) ;
        Format.fprintf fmt "Goal @[<hov 2>%a@]@]@." F.pp_pred vc.goal ;
      end
    else
      Pcond.dump_bundle ~clause:"Context" ~goal:vc.goal fmt vc.hyps

  let pp_vcs fmt vcs =
    let k = ref 0 in
    Splitter.iter
      (fun tags vc ->
         incr k ;
         begin
           match tags with
           | [] -> ()
           | t::ts ->
             Format.fprintf fmt " (%a" Splitter.pretty t ;
             List.iter (fun t -> Format.fprintf fmt ",%a" Splitter.pretty t) ts ;
             Format.fprintf fmt ")@\n" ;
         end ;
         Format.fprintf fmt "@[<hov 5> (%d) %a@]@\n" !k pp_vc vc)
      vcs

  let pp_gvcs fmt gvcs =
    Gmap.iter_sorted
      (fun goal vcs ->
         let n = Splitter.length vcs in
         Format.fprintf fmt "Goal %a: (%d)@\n" TARGET.pretty goal n ;
         pp_vcs fmt vcs ;
      ) gvcs

  let pretty fmt wp =
    begin
      (match wp.sigma with None -> () | Some s ->
          Format.fprintf fmt "Sigma:@[<hov 2>%a@]@\n" Sigma.pretty s) ;
      pp_gvcs fmt wp.vcs ;
    end

  (* -------------------------------------------------------------------------- *)
  (* --- Utilities                                                          --- *)
  (* -------------------------------------------------------------------------- *)

  let empty_vc = {
    hyps = Conditions.nil ;
    goal = p_true ;
    vars = V.empty ;
    warn = W.empty ;
    deps = D.empty ;
    path = S.empty ;
  }

  let sigma_opt = function None -> Sigma.create () | Some s -> s
  let sigma_at w = sigma_opt w.sigma
  let sigma_union s1 s2 =
    match s1 , s2 with
    | None , s | s , None -> sigma_opt s , Passive.empty , Passive.empty
    | Some s1 , Some s2 -> Sigma.merge s1 s2
  let merge_sigma s1 s2 =
    match s1 , s2 with
    | None , s | s , None -> s , Passive.empty , Passive.empty
    | Some s1 , Some s2 -> let s,p1,p2 = Sigma.merge s1 s2 in Some s,p1,p2

  let join_with s = function None -> Passive.empty | Some s' -> Sigma.join s s'

  let occurs_vc vc x =
    Vars.mem x vc.vars || Conditions.occurs x vc.hyps

  let intersect_vc vc p =
    Vars.intersect (F.varsp p) vc.vars || Conditions.intersect p vc.hyps

  let state_vc ?descr ?stmt sigma state vc =
    let path = match stmt with
      | None -> vc.path
      | Some s -> S.add s vc.path in
    let hyps =
      if not (Wp_parameters.RTE.get()) then vc.hyps
      else Conditions.domain [M.is_well_formed sigma] vc.hyps
    in
    let hyps = Conditions.state ?stmt ?descr state hyps in
    { vc with path ; hyps }

  let assume_vc ?descr ?hpid ?stmt ?warn
      ?(filter=false) ?(domain=false) ?(init=false)
      hs vc =
    if (hs = [] && warn = None) ||
       (filter && not (List.exists (intersect_vc vc) hs))
    then vc else
      let path = match stmt with
        | None -> vc.path
        | Some s -> S.add s vc.path in
      let deps = match hpid with
        | None -> [] | Some p -> [WpPropId.property_of_id p] in
      let dset = List.fold_right D.add deps vc.deps in
      let wrns = match warn with
        | None -> vc.warn
        | Some w -> Warning.Set.union w vc.warn in
      let hyps = Conditions.assume
          ?descr ?stmt ?warn ~deps ~init ~domain
          (F.p_conj hs) vc.hyps
      in {
        hyps = hyps ;
        goal = vc.goal ;
        vars = vc.vars ;
        warn = wrns ;
        deps = dset ;
        path = path ;
      }

  (* -------------------------------------------------------------------------- *)
  (* --- Branching                                                          --- *)
  (* -------------------------------------------------------------------------- *)

  let branch_vc ~stmt ~warn cond vc1 vc2 =
    let hyps , goal =
      if F.eqp vc1.goal vc2.goal then
        begin
          Conditions.branch ~stmt ~warn cond vc1.hyps vc2.hyps ,
          vc1.goal
        end
      else
        let k = F.e_var (Lang.freshvar ~basename:"K" Logic.Bool) in
        let p = F.p_equal k F.e_true in
        let q = F.p_equal k F.e_false in
        let h1 = Conditions.assume p vc1.hyps in
        let h2 = Conditions.assume q vc2.hyps in
        (Conditions.branch ~stmt ~warn cond h1 h2 , F.p_if p vc1.goal vc2.goal)
    in
    {
      hyps = hyps ;
      goal = goal ;
      vars = V.union vc1.vars vc2.vars ;
      deps = D.union vc1.deps vc2.deps ;
      warn = W.union vc1.warn vc2.warn ;
      path = S.union vc1.path vc2.path ;
    }

  (* -------------------------------------------------------------------------- *)
  (* --- Merging                                                            --- *)
  (* -------------------------------------------------------------------------- *)

  let merge_vc vc1 vc2 =
    let hyps , goal =
      if F.eqp vc1.goal vc2.goal then
        Conditions.merge [vc1.hyps;vc2.hyps] , vc1.goal
      else
        let k = F.e_var (Lang.freshvar ~basename:"K" Logic.Bool) in
        let p = F.p_equal k F.e_true in
        let q = F.p_equal k F.e_false in
        let h1 = Conditions.assume ~descr:"Merge Left" p vc1.hyps in
        let h2 = Conditions.assume ~descr:"Merge Right" q vc2.hyps in
        (Conditions.merge [h1 ; h2] , F.p_if p vc1.goal vc2.goal)
    in
    {
      hyps = hyps ;
      goal = goal ;
      vars = V.union vc1.vars vc2.vars ;
      deps = D.union vc1.deps vc2.deps ;
      warn = W.union vc1.warn vc2.warn ;
      path = S.union vc1.path vc2.path ;
    }

  let merge_vcs = function
    | [] -> empty_vc
    | [vc] -> vc
    | vcs ->
      let hyps = Conditions.merge (List.map (fun vc -> vc.hyps) vcs) in
      let goal = p_all (fun vc -> vc.goal) vcs in
      let vars = List.fold_left (fun d vc -> V.union d vc.vars) V.empty vcs in
      let deps = List.fold_left (fun d vc -> D.union d vc.deps) D.empty vcs in
      let warn = List.fold_left (fun d vc -> W.union d vc.warn) W.empty vcs in
      let path = List.fold_left (fun d vc -> S.union d vc.path) S.empty vcs in
      { hyps = hyps ;
        goal = goal ;
        vars = vars ;
        deps = deps ;
        warn = warn ;
        path = path }

  (* -------------------------------------------------------------------------- *)
  (* --- Merging and Branching with Splitters                               --- *)
  (* -------------------------------------------------------------------------- *)

  let gmerge = Gmap.union (fun _gid -> Splitter.union merge_vc)

  let gmap phi vcs =
    Gmap.map (Splitter.map phi) vcs

  let gbranch ~left ~both ~right vcs1 vcs2 =
    Gmap.merge
      (fun _g w1 w2 ->
         match w1 , w2 with
         | None , None -> None
         | Some vcs1 , None ->
           Some (Splitter.map left vcs1)
         | None , Some vcs2 ->
           Some (Splitter.map right vcs2)
         | Some vcs1 , Some vcs2 ->
           Some (Splitter.merge ~left ~both ~right vcs1 vcs2)
      ) vcs1 vcs2

  let merge_all_vcs : vc Splitter.t Gmap.t list -> vc Splitter.t Gmap.t =
    fun cases ->
    let targets = List.fold_left
        (fun goals vcs -> Gset.union goals (Gmap.domain vcs))
        Gset.empty cases in
    let goal g vcs =
      try
        let vcs = Gmap.find g vcs in
        if TARGET.is_smoke_test g
        then Splitter.unmark merge_vcs vcs
        else vcs
      with Not_found -> Splitter.empty in
    Gset.mapping
      (fun g -> Splitter.merge_all merge_vcs (List.map (goal g) cases))
      targets

  let passify_vc pa vc =
    let hs = Passive.conditions pa (occurs_vc vc) in
    assume_vc hs vc

  let passify_vcs pa vcs =
    if Passive.is_empty pa then vcs
    else gmap (passify_vc pa) vcs

  (* -------------------------------------------------------------------------- *)
  (* --- Merge for Calculus                                                 --- *)
  (* -------------------------------------------------------------------------- *)

  let empty = {
    sigma = None ;
    effects = Eset.empty ;
    vcs = Gmap.empty ;
  }

  let has_init wenv =
    let frame = wenv.frame in
    let init = L.mem_at_frame frame Clabels.init in
    let domain = Sigma.domain init in
    not (M.Heap.Set.is_empty domain)

  let merge wenv wp1 wp2 =
    L.in_frame wenv.frame
      (fun () ->
         let sigma,pa1,pa2 = merge_sigma wp1.sigma wp2.sigma in
         let effects = Eset.union wp1.effects wp2.effects in
         let vcs1 = passify_vcs pa1 wp1.vcs in
         let vcs2 = passify_vcs pa2 wp2.vcs in
         let vcs = gmerge vcs1 vcs2 in
         { sigma = sigma ; vcs = vcs ; effects = effects }
      ) ()

  (* -------------------------------------------------------------------------- *)
  (* --- Environment                                                        --- *)
  (* -------------------------------------------------------------------------- *)

  let new_env ?lvars kf =
    let frame = L.frame kf in
    let env = L.in_frame frame (L.mk_env ?lvars) () in
    { frame = frame ; main = env }

  let in_wenv
      (wenv:t_env) (wp:t_prop)
      (phi:L.env -> t_prop -> 'a) : 'a =
    L.in_frame wenv.frame
      (fun wp ->
         match wp.sigma with
         | None ->
           let s = Sigma.create () in
           phi (L.move_at wenv.main s) { wp with sigma = Some s }
         | Some s ->
           phi (L.move_at wenv.main s) wp) wp

  (* -------------------------------------------------------------------------- *)
  (* --- Compilation of Goals                                               --- *)
  (* -------------------------------------------------------------------------- *)

  let introduction pred =
    let hs , goal = Conditions.forall_intro pred in
    let xs = List.fold_left
        (fun xs h -> Vars.union xs (F.varsp h))
        (F.varsp goal) hs
    in xs , hs , goal

  let add_vc
      target ?(warn=Warning.Set.empty) ?(deps=Property.Set.empty) pred vcs =
    let xs , hs , goal = introduction pred in
    let hyps = Conditions.intros hs Conditions.nil in
    let vc = { empty_vc with goal ; vars=xs ; hyps ; warn ; deps } in
    Gmap.add target (Splitter.singleton vc) vcs

  (* ------------------------------------------------------------------------ *)
  (* --- Compilation of Effects                                           --- *)
  (* ------------------------------------------------------------------------ *)

  let cc_effect env pid (ainfo:WpPropId.assigns_desc) : effect option =
    let from = ainfo.WpPropId.a_label in
    let sigma = L.mem_frame from in
    let authorized_region =
      L.assigned_of_assigns
        (match ainfo.a_kind with
         | StmtAssigns -> L.move_at env sigma
         | LoopAssigns -> env)
        ainfo.a_assigns
    in match authorized_region with
    | None -> None
    | Some region ->
      let post = match ainfo.a_kind with
        | LoopAssigns -> true
        | StmtAssigns -> NormAtLabels.has_postassigns ainfo.a_assigns
      in Some {
        e_pid = pid ;
        e_post = post ;
        e_label = from ;
        e_valid = sigma ;
        e_region = region ;
        e_warn = Warning.Set.empty ;
      }

  let cc_posteffect e vcs =
    if not e.e_post then vcs else
      let vc = { empty_vc with vars = L.vars e.e_region } in
      Gmap.add (Gposteffect e.e_pid) (Splitter.singleton vc) vcs

  (* -------------------------------------------------------------------------- *)
  (* --- WP RULES : adding axioms, hypotheses and goals                     --- *)
  (* -------------------------------------------------------------------------- *)

  let add_axiom _id _l = ()

  let add_hyp ?for_pid wenv (hpid,predicate) wp = in_wenv wenv wp
      (fun env wp ->
         let outcome = Warning.catch
             ~severe:false ~effect:"Skip hypothesis"
             (L.pred `Negative env) predicate in
         let warn,hs = match outcome with
           | Warning.Result(warn,p) -> warn , [p]
           | Warning.Failed warn -> warn , []
         in
         let assume_vc target vcs = match for_pid with
           | Some id when not @@ PropId.equal id (TARGET.prop_id target) -> vcs
           | _ -> Splitter.map (assume_vc ~hpid ~warn hs) vcs
         in
         let vcs = Gmap.mapi assume_vc wp.vcs in
         { wp with vcs = vcs })

  let add_goal wenv (gpid,predicate) wp = in_wenv wenv wp
      (fun env wp ->
         let outcome = Warning.catch
             ~severe:true ~effect:"Degenerated goal"
             (L.pred `Positive env) predicate in
         let warn,goal = match outcome with
           | Warning.Result(warn,goal) -> warn,goal
           | Warning.Failed warn -> warn,F.p_false
         in
         let vcs = add_vc (Gprop gpid) ~warn goal wp.vcs in
         { wp with vcs = vcs })

  let add_subgoal wenv (gpid,_) ?deps predicate stmt src wp = in_wenv wenv wp
      (fun env wp ->
         let outcome = Warning.catch
             ~severe:true ~effect:"Degenerated goal"
             (L.pred `Positive env) predicate in
         let warn,goal = match outcome with
           | Warning.Result(warn,goal) -> warn,goal
           | Warning.Failed warn -> warn,F.p_false
         in
         let vcs = add_vc (Gsource(gpid, stmt, src)) ~warn ?deps goal wp.vcs in
         { wp with vcs = vcs })

  let add_assigns wenv (gpid,ainfo) wp = in_wenv wenv wp
      begin fun env wp ->
        let outcome = Warning.catch
            ~severe:true ~effect:"Degenerated goal"
            (cc_effect env gpid) ainfo
        in match outcome with
        | Warning.Result (_,None) -> wp
        | Warning.Result (warn,Some e) ->
          let e = { e with e_warn = warn } in
          let effects = Eset.add e wp.effects in
          let vcs = cc_posteffect e wp.vcs in
          { wp with effects = effects ; vcs = vcs }
        | Warning.Failed warn ->
          let vcs = add_vc (Gprop gpid) ~warn p_false wp.vcs in
          { wp with vcs = vcs }
      end

  let add_warnings wrns vcs =
    gmap (fun vc -> { vc with warn = W.union wrns vc.warn }) vcs

  (* -------------------------------------------------------------------------- *)
  (* --- WP RULE : use assigns clause                                       --- *)
  (* -------------------------------------------------------------------------- *)

  let assigns_condition (region : L.region) (e:effect) : F.pred =
    let unfold = Wp_parameters.UnfoldAssigns.get () in
    L.check_assigns ~unfold e.e_valid ~written:region ~assignable:e.e_region

  exception COLLECTED

  let is_collected vcs p =
    try
      Gmap.iter
        (fun target vcs ->
           let q = TARGET.prop_id target in
           if P.equal p q && Splitter.length vcs > 0 then raise COLLECTED
        ) vcs ;
      false
    with COLLECTED -> true

  let check_nothing effects vcs =
    Eset.fold
      (fun e vcs ->
         if is_collected vcs e.e_pid then vcs else
           Gmap.add (Gprop e.e_pid) (Splitter.singleton empty_vc) vcs
      ) effects vcs

  let check_assigns sloc source ?(warn=Warning.Set.empty) region effects vcs =
    Eset.fold
      (fun e vcs ->
         let xs,hs,goal = introduction (assigns_condition region e) in
         let warn = Warning.Set.union warn e.e_warn in
         let setup vc =
           { vc with
             warn = warn ;
             hyps = Conditions.intros hs vc.hyps ;
             goal = goal ;
             vars = xs }
         in
         let group =
           if not e.e_post then
             Splitter.singleton (setup empty_vc)
           else
             try Splitter.map setup (Gmap.find (Gposteffect e.e_pid) vcs)
             with Not_found ->
               Wp_parameters.fatal "Missing post-effect for %a"
                 WpPropId.pretty e.e_pid
         in
         let target = match sloc with
           | None -> Gprop e.e_pid
           | Some stmt -> Gsource(e.e_pid,stmt,source)
         in
         Gmap.add target group vcs
      ) effects vcs

  let do_assigns ?descr ?stmt ~source ?hpid ?warn sequence
      ~assigned effects vcs =
    let vcs = check_assigns stmt source ?warn assigned effects vcs in
    let eqmem = A.apply_assigns sequence assigned in
    gmap (assume_vc ?descr ?hpid ?stmt ?warn eqmem) vcs

  let do_assigns_everything ?stmt ?warn effects vcs =
    Eset.fold
      (fun e vcs ->
         let target = match stmt with
           | None -> Gprop e.e_pid
           | Some s -> Gsource(e.e_pid,s,FromCode)
         in
         add_vc target ?warn F.p_false vcs)
      effects vcs

  let cc_assigned env kind froms =
    let dummy = Sigma.create () in
    let r0 = L.assigned_of_froms (L.move_at env dummy) froms in
    let d0 = A.domain r0 in
    let s1 = L.current env in
    let s0 = Sigma.havoc s1 d0 in
    let sref = match kind with
      | StmtAssigns -> s0
      | LoopAssigns -> s1
    in
    let cc_assigned = L.assigned_of_froms (L.move_at env sref) in
    let assigned = cc_assigned froms in
    let sequence = { pre=s0 ; post=s1 } in
    sequence , assigned

  let use_assigns wenv hpid ainfo wp = in_wenv wenv wp
      begin fun env wp ->
        let stmt = ainfo.a_stmt in
        match ainfo.a_assigns with

        | WritesAny ->
          let sigma = Sigma.havoc_any ~call:false (L.current env) in
          let vcs = do_assigns_everything ?stmt wp.effects wp.vcs in
          { sigma = Some sigma ; vcs=vcs ; effects = wp.effects }

        | Writes froms ->
          let kind = ainfo.WpPropId.a_kind in
          let outcome =
            Warning.catch ~severe:true ~effect:"Assigns everything"
              (cc_assigned env kind) froms
          in
          match outcome with
          | Warning.Result(warn,(sequence,assigned)) ->
            let vcs =
              do_assigns ~source:FromCode
                ?hpid ?stmt ~warn sequence
                ~assigned
                wp.effects wp.vcs in
            { sigma = Some sequence.pre ; vcs=vcs ; effects = wp.effects }
          | Warning.Failed warn ->
            let sigma = Sigma.havoc_any ~call:false (L.current env) in
            let vcs = do_assigns_everything ?stmt ~warn wp.effects wp.vcs in
            { sigma = Some sigma ; vcs=vcs ; effects = wp.effects }
      end

  (* -------------------------------------------------------------------------- *)
  (* --- WP RULE : label                                                    --- *)
  (* -------------------------------------------------------------------------- *)

  let is_stopeffect l e = Clabels.equal l e.e_label
  let not_posteffect es target _vcs = match target with
    | Gposteffect p -> not (Eset.exists (fun e -> P.equal p e.e_pid) es)
    | _ -> true

  let state_vcs stmt sigma vcs =
    try
      let descr : string option = match stmt with
        | None | Some { labels=[] } -> None
        | Some { labels = lbl::_ } ->
          Some (Pretty_utils.to_string Printer.pp_label lbl) in
      let state = Mstate.state state sigma in
      gmap (state_vc ?descr ?stmt sigma state) vcs
    with Not_found -> vcs

  let label wenv stmt label wp =
    if Clabels.is_here label then wp else
      in_wenv wenv wp
        (fun env wp ->
           let frame = L.get_frame () in
           let s_here = L.current env in
           let s_frame =
             if L.has_at_frame frame label then
               L.mem_at_frame frame label
             else
               (L.set_at_frame frame label s_here ; s_here) in
           let pa = Sigma.join s_here s_frame in
           let stop,effects = Eset.partition (is_stopeffect label) wp.effects in
           let vcs = Gmap.filter (not_posteffect stop) wp.vcs in
           let vcs = passify_vcs pa vcs in
           let vcs = check_nothing stop vcs in
           let vcs = state_vcs stmt s_here vcs in
           { sigma = Some s_frame ; vcs=vcs ; effects=effects })

  (* -------------------------------------------------------------------------- *)
  (* --- WP RULE : assignation                                              --- *)
  (* -------------------------------------------------------------------------- *)

  let cc_lval env lv =
    let obj = Ctypes.object_of (Cil.typeOfLval lv) in
    let dummy = Sigma.create () in
    let l0 = C.lval dummy lv in
    let s2 = L.current env in
    let domain = M.domain obj l0 in
    let s1 = Sigma.havoc s2 domain in
    let loc = C.lval s1 lv in
    let seq = { pre=s1 ; post=s2 } in
    obj , domain , seq , loc

  let cc_stored lv seq loc obj expr =
    let intercept_volatile kind lv =
      let warn = "unsafe " ^ kind ^ "-access to volatile l-value" in
      Cil.isVolatileLval lv && Cvalues.volatile ~warn ()
    in
    if intercept_volatile "write" lv then None
    else
      let value = match expr.enode with
        | Lval lv when not @@ intercept_volatile "read" lv ->
          M.copied seq obj loc (C.lval seq.pre lv)
        | _ ->
          (* Note: a volatile lval will be compiled to an unknown value *)
          M.stored seq obj loc (C.val_of_exp seq.pre expr)
      in
      let init = match expr.enode with
        | Lval lv when intercept_volatile "read" lv ->
          M.stored_init seq obj loc (Cvalues.initialized_obj obj)
        | Lval lv when Cil.(isStructOrUnionType @@ typeOfLval lv) ->
          M.copied_init seq obj loc (C.lval seq.pre lv)
        | _ ->
          M.stored_init seq obj loc (Cvalues.initialized_obj obj)
      in
      Some (value @ init)

  let assign wenv stmt lv expr wp = in_wenv wenv wp
      begin fun env wp ->
        let outcome = Warning.catch
            ~severe:true ~effect:"Assigns everything (unknown l-value)"
            (cc_lval env) lv in
        match outcome with
        | Warning.Failed warn ->
          (* L-Value is unknown *)
          let sigma = Sigma.havoc_any ~call:false (L.current env) in
          let vcs = do_assigns_everything ~stmt ~warn wp.effects wp.vcs in
          { sigma = Some sigma ; vcs=vcs ; effects = wp.effects }
        | Warning.Result(l_warn,(obj,dom,seq,loc)) ->
          (* L-Value has been translated *)
          let assigned = [obj,Sloc loc] in
          let outcome = Warning.catch
              ~severe:false ~effect:"Havoc l-value (unknown r-value)"
              (cc_stored lv seq loc obj) expr in
          match outcome with
          | Warning.Failed r_warn
          | Warning.Result(r_warn,None) ->
            (* R-Value is unknown or L-Value is volatile *)
            let warn = Warning.Set.union l_warn r_warn in
            let vcs = do_assigns ~source:FromCode
                ~stmt ~warn seq ~assigned wp.effects wp.vcs in
            { sigma = Some seq.pre ; vcs=vcs ; effects = wp.effects }
          | Warning.Result(r_warn,Some stored) ->
            (* R-Value and effects has been translated *)
            let warn = Warning.Set.union l_warn r_warn in
            let ft = M.Heap.Set.fold_sorted
                (fun chunk ft -> M.Sigma.get seq.post chunk :: ft) dom []
            in
            let update vc =
              if List.exists (occurs_vc vc) ft
              then
                let eqs = List.map Cvalues.equation stored in
                assume_vc ~stmt ~warn eqs vc
              else vc in
            let vcs = gmap update wp.vcs in
            let vcs =
              check_assigns (Some stmt) FromCode assigned wp.effects vcs in
            { sigma = Some seq.pre ; vcs=vcs ; effects = wp.effects }
      end

  (* -------------------------------------------------------------------------- *)
  (* --- WP RULE : return statement                                         --- *)
  (* -------------------------------------------------------------------------- *)

  let return wenv stmt result wp =
    match result with
    | None -> wp
    | Some exp ->
      in_wenv wenv wp
        begin fun env wp ->
          let compile () =
            let sigma = L.current env in
            let vr = L.result () in
            let tr = L.return () in
            p_equal (C.result sigma tr vr) (C.return sigma tr exp) in
          let outcome = Warning.catch
              ~severe:false ~effect:"Result value discarded (unknown)"
              compile () in
          let warn, condition =
            match outcome with
            | Warning.Failed warn ->
              warn , p_true
            | Warning.Result(warn,condition) ->
              warn , condition in
          let vcs = gmap (
              assume_vc ~descr:"Return" ~stmt ~warn [condition]
            ) wp.vcs in
          { wp with vcs = vcs }
        end

  (* -------------------------------------------------------------------------- *)
  (* --- WP RULE : conditional                                              --- *)
  (* -------------------------------------------------------------------------- *)

  let condition ~descr ?stmt ?warn pa h vc =
    passify_vc pa (assume_vc ?stmt ?warn ~descr h vc)

  let mark ?(smoke=false) m = function
    | None -> Splitter.empty
    | Some s -> if smoke then s else Splitter.group m merge_vcs s

  let random () =
    let v = Lang.freshvar ~basename:"cond" Logic.Bool in
    F.p_bool (F.e_var v)

  let weight vcs =
    Gmap.fold (fun _g s n -> n + Splitter.length s) vcs 0

  let test wenv stmt exp wp1 wp2 = L.in_frame wenv.frame
      (fun () ->
         let sigma,pa1,pa2 = sigma_union wp1.sigma wp2.sigma in
         let warn,cond =
           match Warning.catch ~source:"Condition"
                   ~severe:false ~effect:"Skip condition value"
                   (C.cond sigma) exp
           with
           | Warning.Result(warn,cond) -> warn,cond
           | Warning.Failed(warn) -> warn,random()
         in
         let effects = Eset.union wp1.effects wp2.effects in
         let dosplit =
           Wp_parameters.Split.get () &&
           let n1 = weight wp1.vcs in
           let n2 = weight wp2.vcs in
           let nm = Wp_parameters.SplitMax.get () in
           n1 + n2 <= nm in
         let vcs =
           if dosplit then
             let cneg = p_not cond in
             let vcs1 =
               gmap (condition pa1 ~stmt ~warn ~descr:"Then" [cond]) wp1.vcs in
             let vcs2 =
               gmap (condition pa2 ~stmt ~warn ~descr:"Else" [cneg]) wp2.vcs in
             Gmap.merge
               (fun g w1 w2 ->
                  let smoke = TARGET.is_smoke_test g in
                  let s1 = mark ~smoke (Splitter.if_then stmt) w1 in
                  let s2 = mark ~smoke (Splitter.if_else stmt) w2 in
                  Some (Splitter.union (merge_vc) s1 s2)
               ) vcs1 vcs2
           else
             let vcs1 = passify_vcs pa1 wp1.vcs in
             let vcs2 = passify_vcs pa2 wp2.vcs in
             gbranch
               ~left:(assume_vc ~descr:"Then" ~stmt ~warn [cond])
               ~right:(assume_vc ~descr:"Else" ~stmt ~warn [p_not cond])
               ~both:(branch_vc ~stmt ~warn cond)
               vcs1 vcs2
         in
         { sigma = Some sigma ; vcs=vcs ; effects=effects }) ()

  (* -------------------------------------------------------------------------- *)
  (* --- WP RULE : switch                                                   --- *)
  (* -------------------------------------------------------------------------- *)

  let rec cc_case_values ks vs sigma = function
    | [] -> ks , vs
    | e::es ->
      match Ctypes.get_int64 e with
      | Some k ->
        cc_case_values (k::ks) (F.e_int64 k::vs) sigma es
      | None ->
        cc_case_values ks (C.val_of_exp sigma e::vs) sigma es

  let cc_group_case stmt warn descr tag pa cond vcs : vc Splitter.t Gmap.t =
    Gmap.map
      (fun s ->
         Splitter.map
           (condition ~descr ~warn ~stmt pa cond)
           (Splitter.group tag merge_vcs s)
      ) vcs

  let cc_case stmt warn sigma v (es,wp) =
    let ks,vs = cc_case_values [] [] sigma es in
    let pa = join_with sigma wp.sigma in
    let eq = p_any (p_equal v) vs in
    let msg = match ks with
      | [k] -> "Case " ^ Int64.to_string k
      | _ -> "Cases " ^ String.concat "," (List.map Int64.to_string ks) in
    let tag = Splitter.switch_cases stmt ks in
    vs , cc_group_case stmt warn msg tag pa [eq] wp.vcs

  let cc_default stmt sigma neq default =
    let pa = join_with sigma default.sigma in
    cc_group_case stmt W.empty "Default"
      (Splitter.switch_default stmt) pa neq default.vcs

  let switch wenv stmt exp cases default = L.in_frame wenv.frame
      (fun () ->
         let domain =
           List.fold_left (fun d (_,wp) ->
               match wp.sigma with
               | None -> d
               | Some s -> Sigma.union d (Sigma.domain s)
             ) Sigma.empty cases in
         let sigma = Sigma.havoc (Sigma.create ()) domain in
         let warn,value =
           match Warning.catch ~source:"Switch"
                   ~severe:false ~effect:"Skip switched value"
                   (C.val_of_exp sigma) exp
           with
           | Warning.Result(warn,value) -> warn,value
           | Warning.Failed(warn) ->
             let tau = Lang.tau_of_ctype (Cil.typeOf exp) in
             warn,e_var (Lang.freshvar tau)
         in
         let vcs_cases = List.map (cc_case stmt warn sigma value) cases in
         let neq = List.map (fun (vs,_) -> p_all (p_neq value) vs) vcs_cases in
         let vcs_default = cc_default stmt sigma neq default in
         let vcs = merge_all_vcs ( vcs_default :: List.map snd vcs_cases ) in
         let effects = List.fold_left
             (fun es (_,wp) -> Eset.union es wp.effects)
             default.effects cases in
         { sigma = Some sigma ; effects = effects ; vcs = vcs }) ()

  (* -------------------------------------------------------------------------- *)
  (* --- WP RULES : initial values                                          --- *)
  (* -------------------------------------------------------------------------- *)

  let const wenv v wp = in_wenv wenv wp
      (fun env wp ->
         let shere = L.current env in
         let sinit = L.mem_at env Clabels.init in
         let const_vc = assume_vc
             ~init:true ~filter:true
             ~descr:"Global Constant"
             [C.unchanged shere sinit v]
         in { wp with vcs = gmap const_vc wp.vcs })

  let init wenv var opt_init wp = in_wenv wenv wp
      (fun env wp ->
         let assume = assume_vc ~descr:"Initializer" ~filter:true ~init:true in
         let sigma = L.current env in
         let init_vc vc =
           List.fold_left
             (fun vc (warn,(hv,hi)) -> assume ~warn [hi] (assume ~warn [hv] vc))
             vc (C.init ~sigma var opt_init)
         in { wp with vcs = gmap init_vc wp.vcs })

  (* -------------------------------------------------------------------------- *)
  (* --- WP RULE : tag                                                      --- *)
  (* -------------------------------------------------------------------------- *)

  let loop_step wp = wp
  let loop_entry wp = wp

  (* -------------------------------------------------------------------------- *)
  (* --- WP RULE : call dynamic                                             --- *)
  (* -------------------------------------------------------------------------- *)

  let call_pointer sigma fct =
    let outcome = Warning.catch
        ~severe:true ~effect:"Degenerated goal"
        (C.call sigma) fct in
    match outcome with
    | Warning.Failed warn -> warn,None
    | Warning.Result(warn,floc) -> warn,Some floc

  let call_instance_of gpid (warn,fopt) calls vcs =
    let goal = match fopt with
      | None -> F.p_false
      | Some floc -> F.p_any (C.instance_of floc) calls
    in add_vc (Gprop gpid) ~warn goal vcs

  let call_contract stmt sigma hpid (warn,fopt) (kf,wp) : vc Splitter.t Gmap.t =
    let pa = join_with sigma wp.sigma in
    let tag = Splitter.call stmt kf in
    let descr =
      Printf.sprintf "Instance of '%s'" (Kernel_function.get_name kf) in
    let instance_of vc =
      let hyp = match fopt with
        | None -> F.p_true
        | Some floc -> C.instance_of floc kf
      in assume_vc ~stmt ~warn ~descr ~hpid [hyp] vc
    in
    Gmap.map
      (fun s ->
         Splitter.map
           (fun vc -> passify_vc pa (instance_of vc))
           (Splitter.group tag merge_vcs s)
      ) wp.vcs

  let call_dynamic wenv stmt gpid fct calls = L.in_frame wenv.frame
      begin fun () ->
        let sigma = Sigma.create () in
        let called = call_pointer sigma fct in
        let vcs_calls = List.map (call_contract stmt sigma gpid called) calls in
        let vcs = merge_all_vcs vcs_calls in
        let vcs = call_instance_of gpid called (List.map fst calls) vcs in
        let effects = List.fold_left
            (fun es (_,wp) -> Eset.union es wp.effects) Eset.empty calls in
        { sigma = Some sigma ; vcs = vcs ; effects = effects }
      end ()

  (* -------------------------------------------------------------------------- *)
  (* --- WP RULE : call precondition                                        --- *)
  (* -------------------------------------------------------------------------- *)

  let call_goal_precond wenv _stmt kf es ~pre wp = in_wenv wenv wp
      (fun env wp ->
         let sigma = L.current env in
         let outcome = Warning.catch
             ~severe:true ~effect:"Can not prove call preconditions"
             (List.map (C.exp sigma)) es in
         match outcome with
         | Warning.Failed warn ->
           let vcs = List.fold_left
               (fun vcs (gid,_) -> add_vc (Gprop gid) ~warn p_false vcs)
               wp.vcs pre
           in { wp with vcs = vcs }
         | Warning.Result(warn,vs) ->
           let init = L.mem_at env Clabels.init in
           let call = L.call kf vs in
           let call_e = L.mk_env ~here:sigma () in
           let call_f = L.call_pre init call sigma in
           let vcs = List.fold_left
               (fun vcs (gid,p) ->
                  let outcome = Warning.catch
                      ~severe:true ~effect:"Can not prove call precondition"
                      (L.in_frame call_f (L.pred `Positive call_e)) p in
                  match outcome with
                  | Warning.Result(warn2,goal) ->
                    let warn = W.union warn warn2 in
                    add_vc (Gprop gid) ~warn goal vcs
                  | Warning.Failed warn2 ->
                    let warn = W.union warn warn2 in
                    add_vc (Gprop gid) ~warn p_false vcs
               ) wp.vcs pre
           in { wp with vcs = vcs })

  (* -------------------------------------------------------------------------- *)
  (* --- WP RULE : call terminates                                          --- *)
  (* -------------------------------------------------------------------------- *)

  let call_terminates wenv stmt kf args (id, caller_t) ?callee_t wp =
    in_wenv wenv wp
      (fun env wp ->
         let outcome = Warning.catch
             ~severe:true
             ~effect:"Considering that call must always terminate"
             (L.pred `Positive env) caller_t
         in
         let warn, caller_t = match outcome with
           | Warning.Failed warn -> warn, p_true
           | Warning.Result (warn, p) -> warn, p
         in
         let prove_terminates ~warn p =
           add_vc (Gsource(id, stmt, FromCall)) ~warn (p_imply caller_t p)
         in
         let sigma = L.current env in
         let outcome = Warning.catch
             ~severe:true
             ~effect:"Considering non terminating callee"
             (List.map (C.exp sigma)) args in
         match outcome with
         | Warning.Failed warn2 ->
           let warn = W.union warn warn2 in
           let vcs = prove_terminates ~warn p_false wp.vcs in
           { wp with vcs = vcs }
         | Warning.Result(warn2, args) ->
           let warn = W.union warn warn2 in
           let compile_callee = function
             | None ->
               Warning.error "No terminates clause for %a"
                 Kernel_function.pretty kf
             | Some callee_t ->
               let init = L.mem_at env Clabels.init in
               let call = L.call kf args in
               let call_e = L.mk_env ~here:sigma () in
               let call_f = L.call_pre init call sigma in
               L.in_frame call_f (L.pred `Positive call_e) callee_t
           in
           let outcome =
             Warning.catch
               ~severe:true ~effect:"Considering non terminating callee"
               compile_callee callee_t
           in
           let warn2, callee_t = match outcome with
             | Warning.Failed warn -> warn, p_false
             | Warning.Result(warn,callee_t) -> warn, callee_t
           in
           let warn = W.union warn warn2 in
           let vcs = prove_terminates ~warn callee_t wp.vcs in
           { wp with vcs = vcs })

  (* -------------------------------------------------------------------------- *)
  (* --- WP RULE : call decreases                                           --- *)
  (* -------------------------------------------------------------------------- *)

  let call_decreases wenv stmt kf args (id, caller_d) ?caller_t ?callee_d wp =
    in_wenv wenv wp
      (fun env wp ->
         let compile_caller_t caller_t =
           if not @@ Wp_parameters.TerminatesVariantHyp.get () then p_true
           else match caller_t with
             | None -> p_true
             | Some t -> (L.pred `Positive env) t
         in
         let outcome = Warning.catch
             ~severe:true
             ~effect:"Considering that call must always decrease"
             compile_caller_t caller_t
         in
         let warn, caller_t = match outcome with
           | Warning.Failed warn -> warn, p_true
           | Warning.Result (warn, p) -> warn, p
         in
         let prove_decreases ~warn p =
           add_vc (Gsource(id, stmt, FromCall)) ~warn (p_imply caller_t p)
         in
         let sigma = L.current env in
         let outcome = Warning.catch
             ~severe:true
             ~effect:"Considering non decreasing call"
             (List.map (C.exp sigma)) args in
         match outcome with
         | Warning.Failed warn2 ->
           let warn = W.union warn warn2 in
           let vcs = prove_decreases ~warn p_false wp.vcs in
           { wp with vcs = vcs }
         | Warning.Result(warn2, args) ->
           let warn = W.union warn warn2 in
           let init = L.mem_at env Clabels.init in
           let call = L.call kf args in
           let call_e = L.mk_env ~here:sigma () in
           let call_f = L.call_pre init call sigma in
           let compile_decreases (caller_d, callee_d) =
             match caller_d, callee_d with
             | _, None ->
               Warning.error "No decreases clause for %a"
                 Kernel_function.pretty kf
             | (_, r), Some (_, r')
               when not @@ Option.equal Logic_utils.is_same_logic_info r r' ->
               let none : Pretty_utils.sformat = "<None>" in
               Warning.error
                 "On call to %a, relation (%a) does not match caller (%a)"
                 Kernel_function.pretty kf
                 (Pretty_utils.pp_opt ~none Cil_printer.pp_logic_info) r
                 (Pretty_utils.pp_opt ~none Cil_printer.pp_logic_info) r'
             | (caller_d, rel), Some (callee_d,_ ) ->
               let rel caller callee = match rel with
                 | None ->
                   p_and (p_leq e_zero caller) (p_lt callee caller)
                 | Some rel ->
                   (L.in_frame call_f (L.call_pred call_e))
                     rel [] [caller ; callee]
               in
               let caller_d = L.term env caller_d in
               let callee_d =
                 (L.in_frame call_f (L.term call_e)) callee_d in
               rel caller_d callee_d
           in
           let outcome =
             Warning.catch
               ~severe:true ~effect:"Considering non decreasing call"
               compile_decreases (caller_d, callee_d)
           in
           let warn2, pred = match outcome with
             | Warning.Failed warn -> warn, p_false
             | Warning.Result (warn, p) -> warn, p
           in
           let warn = W.union warn warn2 in
           let vcs = prove_decreases ~warn pred wp.vcs in
           { wp with vcs = vcs })


  (* -------------------------------------------------------------------------- *)
  (* --- WP RULE : call postcondition                                       --- *)
  (* -------------------------------------------------------------------------- *)

  type callenv = {
    sigma_pre : sigma ;
    seq_post : sigma sequence ;
    seq_exit : sigma sequence ;
    seq_result : sigma sequence ;
    loc_result : (typ * Ctypes.c_object * loc) option ;
    frame_pre : L.frame ;
    frame_post : L.frame ;
    frame_exit : L.frame ;
  }

  (* --- Computing Call Memory States --- *)

  let cc_result_domain = function
    | Some lv ->
      let dummy = Sigma.create () in
      let tr = Cil.typeOfLval lv in
      let lr = C.lval dummy lv in
      Some (M.domain (Ctypes.object_of tr) lr)
    | None -> Some (M.Heap.Set.empty)

  let cc_call_domain env0 kf es = function
    | WritesAny -> None
    | Writes froms ->
      let dummy = Sigma.create () in
      let vs = List.map (C.exp dummy) es in
      let env = L.move_at env0 dummy in
      let init = L.mem_at env0 Clabels.init in
      let frame = L.call_pre init (L.call kf vs) dummy in
      let cc_froms = L.assigned_of_froms env in
      Some (A.domain (L.in_frame frame cc_froms froms))

  let cc_havoc d s = match d with
    | None -> { pre = Sigma.havoc_any ~call:true s ; post = s }
    | Some domain -> { pre = Sigma.havoc s domain ; post = s }

  let cc_callenv env0 lvr kf es assigns wpost wexit =
    let init = L.mem_at env0 Clabels.init in
    let dom_call = cc_call_domain env0 kf es assigns in
    let dom_vret = cc_result_domain lvr in
    (* Sequences to be considered *)
    let seq_result = cc_havoc dom_vret (sigma_at wpost) in
    let seq_post = cc_havoc dom_call seq_result.pre in
    let seq_exit = cc_havoc dom_call (sigma_at wexit) in
    (* Pre-State *)
    (* Passive: joined later by call_proper *)
    let sigma_pre, _, _ = Sigma.merge seq_post.pre seq_exit.pre in
    let formals = List.map (C.exp sigma_pre) es in
    let call = L.call kf formals in
    let result = match lvr with
      | None -> None
      | Some lv ->
        let tr = Cil.typeOfLval lv in
        let obj = Ctypes.object_of tr in
        let loc = C.lval sigma_pre lv in
        Some (tr,obj,loc)
    in
    {
      sigma_pre = sigma_pre ;
      seq_post = seq_post ;
      seq_exit = seq_exit ;
      seq_result = seq_result ;
      loc_result = result ;
      frame_pre = L.call_pre init call sigma_pre ;
      frame_post = L.call_post init call seq_post ;
      frame_exit = L.call_post init call seq_exit ;
    }

  type call_vcs = {
    vcs_post : vc Splitter.t Gmap.t ;
    vcs_exit : vc Splitter.t Gmap.t ;
  }

  let cc_call_effects stmt cenv env0 assigns wpost wexit =
    match assigns with
    | WritesAny ->
      {
        vcs_post = do_assigns_everything ~stmt wpost.effects wpost.vcs ;
        vcs_exit = do_assigns_everything ~stmt wexit.effects wexit.vcs ;
      }
    | Writes froms ->
      let env = L.move_at env0 cenv.sigma_pre in
      let cc_region = L.assigned_of_froms env in
      let vcs_post =
        let assigned = L.in_frame cenv.frame_post cc_region froms in
        do_assigns ~descr:"Call Effects" ~source:FromCall
          ~stmt cenv.seq_post ~assigned wpost.effects wpost.vcs in
      let vcs_exit =
        let assigned = L.in_frame cenv.frame_exit cc_region froms in
        do_assigns ~descr:"Exit Effects" ~source:FromCall
          ~stmt cenv.seq_exit ~assigned wexit.effects wexit.vcs in
      let vcs_result =
        match cenv.loc_result with
        | None -> vcs_post (* no result *)
        | Some(_,obj,loc) ->
          let assigned = [obj,Sloc loc] in
          do_assigns ~descr:"Return Effects"
            ~source:FromReturn ~stmt cenv.seq_result
            ~assigned wpost.effects vcs_post
      in
      { vcs_post = vcs_result ; vcs_exit = vcs_exit }

  (* --- Compiling Contracts --- *)

  let cc_contract_hyp frame env contract =
    L.in_frame frame
      (List.map (fun (_,p) -> L.pred `Negative env p)) contract

  (* --- Binding Result --- *)

  let cc_result call = match call.loc_result with
    | None -> []
    | Some(tr,obj,loc) ->
      let handler () = [ p_true ] in
      let compile () =
        (* [LC,VP] : the C left unspecified where to compute the lv *)
        (* [LC,BY] : lv computed before, like in Value Analysis *)
        let vr = M.load call.seq_result.post obj loc in
        let re = L.in_frame call.frame_post L.result () in
        let te = L.in_frame call.frame_post L.return () in
        let value = C.result call.sigma_pre tr re in
        [ C.equal_typ tr vr (C.cast tr te (Val value)) ]
      in
      Warning.handle ~handler ~severe:false ~effect:"Hide \\result" compile ()

  let cc_status f_caller f_callee =
    p_equal
      (e_var (L.in_frame f_caller L.status ()))
      (e_var (L.in_frame f_callee L.status ()))

  (* --- Call Rule --- *)

  let call_proper wenv stmt lvr kf es ~pre ~post ~pexit ~assigns ~p_post ~p_exit () =
    let call = cc_callenv wenv.main lvr kf es assigns p_post p_exit in
    let env_pre = L.move_at wenv.main call.sigma_pre in
    let env_post = L.move_at wenv.main call.seq_post.post in
    let env_exit = L.move_at wenv.main call.seq_exit.post in

    (* Compiling specifications *)
    let hs_pre  = cc_contract_hyp call.frame_pre env_pre pre in
    let hs_post = cc_contract_hyp call.frame_post env_post post in
    let hs_exit = cc_contract_hyp call.frame_exit env_exit pexit in

    (* Binding result/status *)
    let hs_post = cc_result call @ hs_post in
    let hs_exit = cc_status wenv.frame call.frame_exit :: hs_exit in

    (* Checking effects (assigns and result) *)
    let ceff = cc_call_effects stmt call wenv.main assigns p_post p_exit in

    (* Applying specifications *)
    let fname = Kernel_function.get_name kf in
    let apply outcome pa hs vcs =
      let descr = Printf.sprintf "%s '%s'" outcome fname in
      gmap (condition ~descr ~stmt pa hs) vcs in

    let pa_post = Sigma.join call.sigma_pre call.seq_post.pre in
    let pa_exit = Sigma.join call.sigma_pre call.seq_exit.pre in

    (* Skip Precond for Caveat mode *)
    let hs_pre = if Wp_parameters.CalleePreCond.get () then hs_pre else [] in

    (* Build the contexts *)
    let cond_post = apply "Call" pa_post (hs_pre @ hs_post) ceff.vcs_post in
    let cond_exit = apply "Exit" pa_exit (hs_pre @ hs_exit) ceff.vcs_exit in

    (* Final vcs *)
    let vcs = gmerge cond_post cond_exit in
    let effects = Eset.union p_post.effects p_exit.effects in
    { sigma = Some call.sigma_pre ; effects=effects ; vcs=vcs }

  let call wenv stmt lvr kf es ~pre ~post ~pexit ~assigns ~p_post ~p_exit
    = L.in_frame wenv.frame
      (fun () ->
         let outcome = Warning.catch
             ~severe:true ~effect:"Call assigns everything"
             (call_proper wenv stmt lvr kf es
                ~pre ~post ~pexit ~assigns ~p_post ~p_exit) () in
         match outcome with
         | Warning.Result(warn , wp) -> { wp with vcs = add_warnings warn wp.vcs }
         | Warning.Failed warn ->
           let v_post = do_assigns_everything ~stmt ~warn p_post.effects p_post.vcs in
           let v_exit = do_assigns_everything ~stmt ~warn p_exit.effects p_exit.vcs in
           let effects = Eset.union p_post.effects p_exit.effects in
           let vcs = gmerge v_post v_exit in
           let sigma = Sigma.create () in
           { sigma = Some sigma ; vcs = vcs ; effects = effects }
      ) ()

  (* -------------------------------------------------------------------------- *)
  (* --- WP RULE : scope                                                    --- *)
  (* -------------------------------------------------------------------------- *)

  let wp_scope env wp ~descr scope xs =
    let post = L.current env in
    let pre = M.alloc post xs in
    let hs = M.scope { pre ; post } scope xs in
    let vcs = gmap (assume_vc ~descr hs) wp.vcs in
    { wp with sigma = Some pre ; vcs = vcs }

  let scope wenv xs sc wp = in_wenv wenv wp
      begin fun env wp ->
        match sc with
        | Mcfg.SC_Global ->
          let hs = M.frame (L.current env) in
          let vcs = gmap (assume_vc ~descr:"Heap" ~domain:true hs) wp.vcs in
          { wp with vcs }
        | Mcfg.SC_Frame_in ->
          wp_scope env wp ~descr:"Frame In" Enter xs
        | Mcfg.SC_Frame_out ->
          wp_scope env wp ~descr:"Frame Out" Leave xs
        | Mcfg.SC_Block_in ->
          wp_scope env wp ~descr:"Block In" Enter xs
        | Mcfg.SC_Block_out ->
          wp_scope env wp ~descr:"Block Out" Leave xs
      end

  (* -------------------------------------------------------------------------- *)
  (* --- WP RULE : close                                                    --- *)
  (* -------------------------------------------------------------------------- *)

  let close wenv wp =
    let guards = L.guards wenv.frame in
    let vcs = gmap
        (fun vc ->
           let gdom = List.filter (intersect_vc vc) guards in
           let hyps = Conditions.domain gdom vc.hyps in
           { vc with hyps = hyps ; vars = Vars.empty }
        ) wp.vcs
    in
    { wp with vcs = vcs }

  (* -------------------------------------------------------------------------- *)
  (* --- WP RULE : froms                                                    --- *)
  (* -------------------------------------------------------------------------- *)

  let cc_from deps hs vc =
    let guards = Lang.get_hypotheses () in
    let hyps = Conditions.assume ~descr:"Bisimulation" (p_conj guards) vc.hyps in
    let p = F.p_hyps (Conditions.extract hyps) vc.goal in
    let alpha = Lang.alpha () in
    let a_hs = List.map (F.p_subst alpha) hs in
    let a_p = F.p_subst alpha p in
    let p = p_hyps a_hs a_p in
    { vc with
      goal = p ; vars = F.varsp p ;
      hyps = Conditions.nil ;
      deps = D.union deps vc.deps ;
    }

  let build_prop_of_from wenv preconds wp = in_wenv wenv wp
      (fun env wp ->
         let sigma = L.mem_frame Clabels.pre in
         let env_pre = L.move_at env sigma in
         let hs = List.map
             (fun (_,p) -> L.pred `Negative env_pre p)
             preconds in
         let ds = List.fold_left
             (fun ds (pid,_) -> D.add (WpPropId.property_of_id pid) ds)
             D.empty preconds in
         let vcs = gmap (cc_from ds hs) wp.vcs in
         { sigma = Some sigma ; effects = Eset.empty ; vcs=vcs })

  (* -------------------------------------------------------------------------- *)
  (* --- WPO Builder                                                        --- *)
  (* -------------------------------------------------------------------------- *)

  let is_trivial vc = F.eqp vc.goal F.p_true

  let is_empty vc =
    is_trivial vc &&
    D.is_empty vc.deps &&
    S.is_empty vc.path &&
    W.is_empty vc.warn

  let make_vcqs target tags vc =
    let vcq = {
      VC_Annot.effect = TARGET.source target ;
      VC_Annot.axioms = None ;
      VC_Annot.goal = GOAL.dummy ;
      VC_Annot.tags = tags ;
      VC_Annot.deps = vc.deps ;
      VC_Annot.path = vc.path ;
      VC_Annot.warn = W.elements vc.warn ;
    } in
    let hyps = Conditions.bundle vc.hyps in
    let goal g = { vcq with VC_Annot.goal = GOAL.make (hyps,g) } in
    match F.p_expr vc.goal with
    | Logic.And gs when Wp_parameters.Split.get () -> Bag.list (List.map goal gs)
    | _ -> Bag.elt (goal vc.goal)

  let make_trivial vc =
    {
      VC_Annot.effect = None ;
      VC_Annot.axioms = None ;
      VC_Annot.goal = GOAL.trivial ;
      VC_Annot.tags = [] ;
      VC_Annot.deps = vc.deps ;
      VC_Annot.path = vc.path ;
      VC_Annot.warn = W.elements vc.warn ;
    }

  let make_oblig index pid vcq =
    {
      po_model = WpContext.get_model () ;
      po_pid = pid ;
      po_sid = "" ;
      po_gid = "" ;
      po_name = "" ;
      po_idx = index ;
      po_formula = GoalAnnot vcq ;
    }

  (* -------------------------------------------------------------------------- *)
  (* --- WPO Grouper                                                        --- *)
  (* -------------------------------------------------------------------------- *)

  module PMAP = Map.Make(P)

  type group = {
    mutable verifs : VC_Annot.t Bag.t ;
    mutable trivial : vc ;
  }

  let group_vc groups target tags vc =
    let pid = TARGET.prop_id target in
    let group =
      try PMAP.find pid !groups
      with Not_found ->
        let g = { verifs = Bag.empty ; trivial = empty_vc } in
        groups := PMAP.add pid g !groups ; g
    in
    if is_trivial vc
    then
      group.trivial <- merge_vc group.trivial vc
    else
      group.verifs <- Bag.concat group.verifs (make_vcqs target tags vc)

  let compile_wp index (wp : t_prop) =
    let groups = ref PMAP.empty in
    let collection = ref Bag.empty in
    Gmap.iter_sorted
      (fun target -> Splitter.iter (group_vc groups target))
      wp.vcs ;
    let model = WpContext.get_model () in
    PMAP.iter
      begin fun pid group ->
        let trivial_wpo =
          let vcq = make_trivial group.trivial in
          Bag.elt (make_oblig index pid vcq)
        in
        let provers_wpo =
          Bag.map (make_oblig index pid) group.verifs
        in
        let mid = WpContext.MODEL.id model in
        let group =
          if is_empty group.trivial then
            if Bag.is_empty provers_wpo
            then trivial_wpo
            else provers_wpo
          else
            Bag.concat trivial_wpo provers_wpo
        in
        WpPropId.split_bag
          begin fun po_pid wpo ->
            let po_sid = WpPropId.get_propid po_pid in
            let po_gid = Printf.sprintf "%s_%s" mid po_sid in
            let po_name = Pretty_utils.to_string WpPropId.pretty_local pid in
            let wpo =
              { wpo with po_pid ; po_sid ; po_gid ; po_name }
            in
            Wpo.add wpo ;
            collection := Bag.append !collection wpo ;
          end
          pid group

      end !groups ;
    !collection

  let register_lemma l = ignore (L.lemma l)

  let compile_lemma l =
    begin
      let id = WpPropId.mk_lemma_id l in
      let def = L.lemma l in
      let model = WpContext.get_model () in
      let vca = {
        Wpo.VC_Lemma.depends = l.lem_depends ;
        Wpo.VC_Lemma.lemma = def ;
        Wpo.VC_Lemma.sequent = None ;
      } in
      let index = match LogicUsage.section_of_lemma l.lem_name with
        | LogicUsage.Toplevel _ -> Wpo.Axiomatic None
        | LogicUsage.Axiomatic a -> Wpo.Axiomatic (Some a.ax_name) in
      let mid = WpContext.MODEL.id model in
      let sid = WpPropId.get_propid id in
      let wpo = {
        Wpo.po_model = model ;
        Wpo.po_gid = Printf.sprintf "%s_%s" mid sid ;
        Wpo.po_sid = sid ;
        Wpo.po_name = Printf.sprintf "Lemma '%s'" l.lem_name ;
        Wpo.po_idx = index ;
        Wpo.po_pid = id ;
        Wpo.po_formula = Wpo.GoalLemma vca ;
      } in
      Wpo.add wpo ; wpo
    end

end

(* -------------------------------------------------------------------------- *)
(* --- VCgen Cache                                                        --- *)
(* -------------------------------------------------------------------------- *)

(* Cache by Model Context *)
let vcgenerators = WpContext.MINDEX.create 1

let vcgen setup driver : (module VCgen) =
  let model = Factory.instance setup driver in
  try WpContext.MINDEX.find vcgenerators model
  with Not_found ->
    let module M = (val Factory.(compiler setup.mheap setup.mvar)) in
    let vcgen = (module VC(M) : VCgen) in
    WpContext.MINDEX.add vcgenerators model vcgen ;
    vcgen

(* -------------------------------------------------------------------------- *)
