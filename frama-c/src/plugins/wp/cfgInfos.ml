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

module Cfg = Interpreted_automata
module Fset = Kernel_function.Set
module Sset = Cil_datatype.Stmt.Set
module Pset = Property.Set
module Shash = Cil_datatype.Stmt.Hashtbl

(* -------------------------------------------------------------------------- *)
(* --- Compute Kernel-Function & CFG Infos for WP                         --- *)
(* -------------------------------------------------------------------------- *)

module CheckPath = Graph.Path.Check(Cfg.G)

type t = {
  body : Cfg.automaton option ;
  checkpath : CheckPath.path_checker option ;
  reachability : WpReached.reachability option ;
  mutable annots : bool; (* has goals to prove *)
  mutable doomed : WpPropId.prop_id Bag.t;
  mutable calls : Kernel_function.Set.t;
  mutable no_variant_loops : Sset.t;
  mutable terminates_deps : Pset.t;
}

(* -------------------------------------------------------------------------- *)
(* --- Getters                                                            --- *)
(* -------------------------------------------------------------------------- *)

let body infos = infos.body
let calls infos = infos.calls
let annots infos = infos.annots
let doomed infos = infos.doomed

let wpreached s = function
  | None -> false
  | Some reachability -> WpReached.smoking reachability s
let smoking infos s = wpreached s infos.reachability

let unreachable infos v =
  match infos.body, infos.checkpath with
  | Some cfg , Some checkpath ->
    not @@ CheckPath.check_path checkpath cfg.entry_point v
  | _ -> true

let terminates_deps infos = infos.terminates_deps

(* -------------------------------------------------------------------------- *)
(* --- Selected Properties                                                --- *)
(* -------------------------------------------------------------------------- *)

let selected ~bhv ~prop pid =
  (prop = [] || WpPropId.select_by_name prop pid) &&
  (bhv = [] || WpPropId.select_for_behaviors bhv pid)

let selected_default ~bhv =
  bhv=[] || List.mem Cil.default_behavior_name bhv

let selected_name ~prop name =
  prop=[] || WpPropId.are_selected_names prop [name]

let selected_assigns ~prop = function
  | Cil_types.WritesAny -> false
  | Writes _ when prop = [] -> true
  | Writes l ->
    let collect_names l (t, _) =
      WpPropId.ident_names t.Cil_types.it_content.term_name @ l
    in
    let names = List.fold_left collect_names ["@assigns"] l in
    WpPropId.are_selected_names prop names

let selected_allocates ~prop = function
  | Cil_types.FreeAllocAny -> false
  | _ -> (selected_name ~prop "@allocates" || selected_name ~prop "@frees")

let selected_precond ~prop ip =
  prop = [] ||
  let tk_name = "@requires" in
  let tp_names = WpPropId.user_pred_names ip.Cil_types.ip_content in
  WpPropId.are_selected_names prop (tk_name :: tp_names)

let selected_postcond ~prop (tk,ip) =
  prop = [] ||
  let tk_name = "@" ^ WpPropId.string_of_termination_kind tk in
  let tp_names = WpPropId.user_pred_names ip.Cil_types.ip_content in
  WpPropId.are_selected_names prop (tk_name :: tp_names)

let selected_requires ~prop (b : Cil_types.funbehavior) =
  List.exists (selected_precond ~prop) b.b_requires

let selected_call ~bhv ~prop kf =
  bhv = [] && List.exists (selected_requires ~prop) (Annotations.behaviors kf)

let selected_clause ~prop name getter kf =
  getter kf <> [] && selected_name ~prop name

let selected_terminates ~prop kf =
  match Annotations.terminates kf with
  | None ->
    Wp_parameters.TerminatesDefinitions.get ()
  | Some ip ->
    let tk_name = "@terminates" in
    let tp_names = WpPropId.user_pred_names ip.Cil_types.ip_content in
    WpPropId.are_selected_names prop (tk_name :: tp_names)

let selected_decreases ~prop kf =
  match Annotations.decreases kf with
  | None -> false
  | Some (it, _) ->
    let tk_name = "@decreases" in
    let tp_names = WpPropId.ident_names it.term_name in
    WpPropId.are_selected_names prop (tk_name :: tp_names)

let selected_disjoint_complete kf ~bhv ~prop =
  selected_default ~bhv &&
  ( selected_clause ~prop "@complete_behaviors" Annotations.complete kf ||
    selected_clause ~prop "@disjoint_behaviors" Annotations.disjoint kf )

let selected_bhv ~smoking ~bhv ~prop (b : Cil_types.funbehavior) =
  (bhv = [] || List.mem b.b_name bhv) &&
  begin
    (selected_assigns ~prop b.b_assigns) ||
    (selected_allocates ~prop b.b_allocation) ||
    (smoking && b.b_requires <> []) ||
    (List.exists (selected_postcond ~prop) b.b_post_cond)
  end

let selected_main_bhv ~bhv ~prop (b : Cil_types.funbehavior) =
  (bhv = [] || List.mem b.b_name bhv) && (selected_requires ~prop b)

(* -------------------------------------------------------------------------- *)
(* --- Calls                                                              --- *)
(* -------------------------------------------------------------------------- *)

let collect_calls ~bhv ?(on_missing_calls=fun _ -> ()) kf stmt =
  let open Cil_types in
  match stmt.skind with
  | Instr(Call(_,fct,_,_)) ->
    begin
      match Kernel_function.get_called fct with
      | Some kf -> Fset.singleton kf
      | None ->
        let bhvs =
          if bhv = []
          then List.map (fun b -> b.b_name) (Annotations.behaviors kf)
          else bhv in
        let calls =
          List.fold_left
            (fun fs bhv -> match Dyncall.get ~bhv stmt with
               | None -> fs
               | Some(_,kfs) -> List.fold_right Fset.add kfs fs
            ) Fset.empty bhvs
        in
        if Fset.is_empty calls then
          on_missing_calls stmt ;
        calls
    end
  | Instr(Local_init(x,ConsInit(vf, args, kind), loc)) ->
    Cil.treat_constructor_as_func
      (fun _r fct _args _loc ->
         match Kernel_function.get_called fct with
         | Some kf -> Fset.singleton kf
         | None -> Fset.empty)
      x vf args kind loc
  | _ -> Fset.empty

(* -------------------------------------------------------------------------- *)
(* --- Recursion                                                          --- *)
(* -------------------------------------------------------------------------- *)

module Callees = WpContext.StaticGenerator(Kernel_function)
    (struct
      type key = Kernel_function.t
      type data = Fset.t * Cil_types.stmt list
      (** functions + unspecified function pointer calls *)

      let name = "Wp.CfgInfos.SCallees"
      let compile = function
        | { Cil_types.fundec = Definition(fd, _ ) } as kf ->
          let stmts = ref [] in
          let on_missing_calls s = stmts := s :: !stmts in
          let fold e s =
            Fset.union e (collect_calls ~on_missing_calls ~bhv:[] kf s)
          in
          let kfs = List.fold_left fold Fset.empty fd.sallstmts in
          kfs, !stmts
        | _ -> Fset.empty, []
    end)

module RecursiveClusters : sig
  val is_recursive : Kernel_function.t -> bool
  val in_cluster : caller:Kernel_function.t -> Kernel_function.t -> bool
end =
struct
  (* Tarjan's algorithm, adapted from:
       http://pauillac.inria.fr/~levy/why3/graph/abs/scct/2/scc.html
     (proved in Why3)
  *)
  let successors kf = fst @@ Callees.get kf

  module HT = Cil_datatype.Kf.Hashtbl

  type env = {
    mutable stack: Fset.elt list;
    mutable id: int;
    table: (Fset.elt, int) Hashtbl.t ;
    clusters: Fset.t option HT.t ;
  }

  let rec unstack_to x ?(cluster=[]) = function
    | [] -> cluster, []
    | y :: s' when Kernel_function.equal y x -> x :: cluster, s'
    | y :: s' -> unstack_to x ~cluster:(y :: cluster) s'

  let rec dfs roots env =
    try
      let v = Fset.choose roots in
      let vn =
        try Hashtbl.find env.table v
        with Not_found -> visit_node v env
      in
      let others_n = dfs (Fset.remove v roots) env in
      min vn others_n
    with Not_found -> max_int
  and visit_node x env =
    let n = env.id in
    Hashtbl.replace env.table x n ;
    env.id <- n + 1;
    env.stack <- x :: env.stack;
    let base = dfs (successors x) env in
    if base < n then base
    else begin
      let (cluster, stack) = unstack_to x env.stack in
      List.iter (fun v -> Hashtbl.replace env.table v max_int) cluster ;
      env.stack <- stack;
      begin match cluster with
        | [ x ] when base = max_int ->
          HT.add env.clusters x None
        | cluster ->
          let set = Some (Fset.of_list cluster) in
          List.iter (fun kf -> HT.add env.clusters kf set) cluster
      end ;
      max_int
    end

  let make_clusters s =
    let e = {
      stack = []; id = 0; table = Hashtbl.create 37; clusters = HT.create 37
    } in
    ignore (dfs s e);
    e.clusters

  module RTable =
    State_builder.Option_ref(HT.Make(Datatype.Option(Fset)))
      (struct
        let name = "Wp.CfgInfo.RecursiveClusters"
        let dependencies = [ Ast.self ]
      end)

  let create () =
    let kfs = ref Kernel_function.Set.empty in
    Globals.Functions.iter(fun kf -> kfs := Fset.add kf !kfs) ;
    make_clusters !kfs

  let table () = RTable.memo create

  let get_cluster kf = HT.find (table ()) kf
  let is_recursive kf =
    (* in a recursive cluster or contains unspecified function pointer call *)
    None <> get_cluster kf || [] <> snd @@ Callees.get kf

  let in_cluster ~caller callee =
    match get_cluster caller with
    | None -> false
    | Some cluster -> Fset.mem callee cluster
end

let is_recursive = RecursiveClusters.is_recursive
let in_cluster = RecursiveClusters.in_cluster

(* -------------------------------------------------------------------------- *)
(* --- No variant loops                                                   --- *)
(* -------------------------------------------------------------------------- *)

let collect_loops_no_variant kf stmt =
  let open Cil_types in
  let fold_no_variant _ = function
    | { annot_content = AVariant v } as ca -> fun _ -> Some (ca, v)
    | _ -> Extlib.id
  in
  let props_of_v ca v =
    let (d, _), (p, _) = CfgAnnot.mk_variant_properties kf stmt ca v in
    Pset.union
      (Pset.singleton @@ WpPropId.property_of_id d)
      (Pset.singleton @@ WpPropId.property_of_id p)
  in
  match stmt.skind with
  | Loop _ ->
    begin match Annotations.fold_code_annot fold_no_variant stmt None with
      | None -> Sset.singleton stmt, Pset.empty
      | Some (ca, v) -> Sset.empty, props_of_v ca (fst v)
    end
  | _ ->
    Sset.empty, Pset.empty

(* -------------------------------------------------------------------------- *)
(* --- Trivially terminates                                               --- *)
(* -------------------------------------------------------------------------- *)

let trivial_terminates = ref 0

let wp_trivially_terminates =
  Emitter.create
    "Trivial Termination"
    [Emitter.Property_status]
    ~correctness:[] (* TBC *)
    ~tuning:[] (* TBC *)

let set_trivially_terminates p hyps =
  incr trivial_terminates ;
  Wp_parameters.result "[CFG] Goal %a : Valid (Trivial)" WpPropId.pp_propid p ;
  let pid = WpPropId.property_of_id p in
  let hyps = Property.Set.elements hyps in
  Property_status.emit wp_trivially_terminates ~hyps pid Property_status.True

(* -------------------------------------------------------------------------- *)
(* --- Memoization Key                                                    --- *)
(* -------------------------------------------------------------------------- *)

module Key =
struct
  type t = {
    kf: Kernel_function.t ;
    smoking: bool ;
    bhv : string list ;
    prop : string list ;
  }

  let compare a b =
    let cmp = Kernel_function.compare a.kf b.kf in
    if cmp <> 0 then cmp else
      let cmp = Stdlib.compare a.smoking b.smoking in
      if cmp <> 0 then cmp else
        let cmp = Stdlib.compare a.bhv b.bhv in
        if cmp <> 0 then cmp else
          Stdlib.compare a.prop b.prop

  let pp_filter kind fmt xs =
    match xs with
    | [] -> ()
    | x::xs ->
      Format.fprintf fmt "~%s:%s" kind x ;
      List.iter (Format.fprintf fmt ",%s") xs

  let pretty fmt k =
    begin
      Kernel_function.pretty fmt k.kf ;
      pp_filter "smoking" fmt (if k.smoking then ["true"] else []) ;
      pp_filter "bhv" fmt k.bhv ;
      pp_filter "prop" fmt k.prop ;
    end

end

(* -------------------------------------------------------------------------- *)
(* --- Main Collection Pass                                               --- *)
(* -------------------------------------------------------------------------- *)

let dead_posts ~bhv ~prop tk (bhvs : CfgAnnot.behavior list) =
  let post ~bhv ~prop tk (b: CfgAnnot.behavior) =
    let assigns, ps =  match tk with
      | Cil_types.Exits -> b.bhv_exit_assigns, b.bhv_exits
      | _ -> b.bhv_post_assigns, b.bhv_ensures in
    let ps = List.filter (selected ~prop ~bhv) @@ List.map fst ps in
    match assigns with
    | WpPropId.AssignsLocations(id, _) -> Bag.list (id :: ps)
    | _ -> Bag.list ps
  in Bag.umap_list (post ~bhv ~prop tk) bhvs

let loop_contract_pids kf stmt =
  match stmt.Cil_types.skind with
  | Loop _ ->
    let invs = CfgAnnot.get_loop_contract kf stmt in
    let add_assigns assigns l =
      match assigns with
      | WpPropId.NoAssignsInfo | AssignsAny _ -> l
      | AssignsLocations (pid, _) -> pid :: l
    in
    let verif_fold CfgAnnot.{ loop_est ; loop_ind } l =
      let l = Option.fold ~none:l ~some:(fun i -> i :: l) loop_est in
      Option.fold ~none:l ~some:(fun i -> i :: l) loop_ind
    in
    List.fold_right verif_fold invs.loop_invariants @@
    List.fold_right add_assigns invs.loop_assigns []
  | _ -> []

let compile Key.{ kf ; smoking ; bhv ; prop } =
  let body, checkpath, reachability =
    if Kernel_function.has_definition kf then
      let cfg = Cfg.get_automaton kf in
      Some cfg,
      Some (CheckPath.create cfg.graph),
      if smoking then Some (WpReached.reachability kf) else None
    else None, None, None
  in
  let infos = {
    body ; checkpath ; reachability ;
    annots = false ;
    doomed = Bag.empty ;
    calls = Fset.empty ;
    no_variant_loops = Sset.empty ;
    terminates_deps = Pset.empty ;
  } in
  let behaviors = Annotations.behaviors kf in
  (* Inits *)
  if Globals.is_entry_point ~when_lib_entry:false kf then
    infos.annots <- List.exists (selected_main_bhv ~bhv ~prop) behaviors ;
  (* Function Body *)
  Option.iter
    begin fun (cfg : Cfg.automaton) ->
      (* Spec Iteration *)
      if selected_decreases ~prop kf ||
         selected_terminates ~prop kf ||
         selected_disjoint_complete kf ~bhv ~prop ||
         (List.exists (selected_bhv ~smoking ~bhv ~prop) behaviors)
      then infos.annots <- true ;
      (* Stmt Iteration *)
      Shash.iter
        (fun stmt (src,_) ->
           let fs = collect_calls ~bhv kf stmt in
           let nv_loops, term_deps = collect_loops_no_variant kf stmt in
           let dead = unreachable infos src in
           let cas = CfgAnnot.get_code_assertions kf stmt in
           let ca_pids =
             Extlib.filter_map_opt
               (fun CfgAnnot.{ code_verified=ca } -> Option.map fst ca) cas in
           let loop_pids = loop_contract_pids kf stmt in
           if dead then
             begin
               if wpreached stmt reachability then
                 (let p = CfgAnnot.get_unreachable kf stmt in
                  infos.doomed <- Bag.append infos.doomed p) ;
               infos.doomed <- Bag.concat infos.doomed (Bag.list ca_pids) ;
               infos.doomed <- Bag.concat infos.doomed (Bag.list loop_pids) ;
             end
           else
             begin
               if not infos.annots &&
                  ( List.exists (selected ~bhv ~prop) ca_pids ||
                    List.exists (selected ~bhv ~prop) loop_pids ||
                    Fset.exists (selected_call ~bhv ~prop) fs )
               then infos.annots <- true ;
               infos.calls <- Fset.union fs infos.calls ;
               infos.no_variant_loops <-
                 Sset.union nv_loops infos.no_variant_loops ;
               infos.terminates_deps <-
                 Pset.union term_deps infos.terminates_deps
             end
        ) cfg.stmt_table ;
      (* Dead Post Conditions *)
      let dead_exit = Fset.is_empty infos.calls in
      let dead_post = unreachable infos cfg.return_point in
      let bhvs =
        if dead_exit || dead_post then
          let exits = not dead_exit in
          List.map (CfgAnnot.get_behavior_goals kf ~exits) behaviors
        else [] in
      if dead_exit then
        infos.doomed <-
          Bag.concat infos.doomed (dead_posts ~bhv ~prop Exits bhvs) ;
      if dead_post then
        infos.doomed <-
          Bag.concat infos.doomed (dead_posts ~bhv ~prop Normal bhvs) ;
    end body ;
  (* Doomed *)
  Bag.iter
    (fun p -> if WpPropId.filter_status p then WpReached.set_unreachable p)
    infos.doomed ;
  (* Termination *)
  let infos =
    if Kernel_function.is_definition kf then
      match CfgAnnot.get_terminates_goal kf with
      | Some (id, _) when selected_terminates ~prop kf ->
        let warning_locs =
          List.map Cil_datatype.Stmt.loc @@ snd @@ Callees.get kf
        in
        if warning_locs <> [] then
          Wp_parameters.warning ~once:true
            "In '%a', no 'calls' specification for statement(s) on \
             line(s): %a, @\nAssuming that they can call '%a'"
            Kernel_function.pretty kf
            (Pretty_utils.pp_list ~sep:", " Cil_datatype.Location.pretty_line)
            warning_locs
            Kernel_function.pretty kf ;
        if is_recursive kf then
          (* Notes:
             - a recursive function never trivially terminates,
             - in absence of decreases, CfgCalculus will warn *)
          begin match CfgAnnot.get_decreases_goal kf with
            | None -> infos
            | Some (id, _) ->
              let deps =
                Pset.add (WpPropId.property_of_id id) infos.terminates_deps
              in
              { infos with terminates_deps = deps }
          end
        else if infos.calls = Fset.empty
             && infos.no_variant_loops = Sset.empty then begin
          set_trivially_terminates id infos.terminates_deps ;
          (* Drop dependencies for this terminates, we've used it. *)
          { infos with terminates_deps = Pset.empty }
        end
        else infos
      | _ -> infos
    else infos
  in
  (* Collected Infos *)
  infos

(* -------------------------------------------------------------------------- *)
(* --- Memoization Data                                                   --- *)
(* -------------------------------------------------------------------------- *)

module Generator = WpContext.StaticGenerator(Key)
    (struct
      type key = Key.t
      type data = t
      let name = "Wp.CfgInfos.Generator"
      let compile = compile
    end)

let get kf ?(smoking=false) ?(bhv=[]) ?(prop=[]) () =
  Generator.get { kf ; smoking ; bhv ; prop }

let clear () = Generator.clear ()

(* -------------------------------------------------------------------------- *)
