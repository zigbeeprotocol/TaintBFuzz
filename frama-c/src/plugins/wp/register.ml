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

let dkey_main = Wp_parameters.register_category "main"
let dkey_raised = Wp_parameters.register_category "raised"
let dkey_script_removed =
  Wp_parameters.register_category "script:show-removed"
let dkey_script_updated =
  Wp_parameters.register_category "script:show-updated"
let dkey_script_incomplete =
  Wp_parameters.register_category "script:show-incomplete"

(* ------------------------------------------------------------------------ *)
(* --- Memory Model Hypotheses                                          --- *)
(* ------------------------------------------------------------------------ *)

let wp_compute_memory_context model =
  let hypotheses_computer = WpContext.compute_hypotheses model in
  let name = WpContext.MODEL.id model in
  MemoryContext.compute name hypotheses_computer

let wp_warn_memory_context model =
  begin
    WpTarget.iter
      begin fun kf ->
        let hypotheses_computer = WpContext.compute_hypotheses model in
        let model = WpContext.MODEL.id model in
        MemoryContext.warn kf model hypotheses_computer
      end
  end

let wp_insert_memory_context model =
  begin
    WpTarget.iter
      begin fun kf ->
        let hyp_computer = WpContext.compute_hypotheses model in
        let model_id = WpContext.MODEL.id model in
        MemoryContext.add_behavior kf model_id hyp_computer
      end
  end

(* ------------------------------------------------------------------------ *)
(* ---  Printing informations                                           --- *)
(* ------------------------------------------------------------------------ *)

let do_wp_print () =
  (* Printing *)
  if Wp_parameters.Print.get () then
    try
      Wpo.iter ~on_goal:(fun _ -> raise Exit) () ;
      Wp_parameters.result "No proof obligations"
    with Exit ->
      Log.print_on_output
        (fun fmt ->
           Wpo.iter
             ~on_axiomatics:(Wpo.pp_axiomatics fmt)
             ~on_behavior:(Wpo.pp_function fmt)
             ~on_goal:(Wpo.pp_goal_flow fmt) ())

let do_wp_print_for goals =
  if Wp_parameters.Print.get () then
    if Bag.is_empty goals
    then Wp_parameters.result "No proof obligations"
    else Log.print_on_output
        (fun fmt -> Bag.iter (Wpo.pp_goal_flow fmt) goals)

let do_wp_report model =
  begin
    let reports = Wp_parameters.Report.get () in
    let jreport = Wp_parameters.ReportJson.get () in
    if reports <> [] || jreport <> "" then
      begin
        let stats = WpReport.fcstat () in
        begin
          match String.split_on_char ':' jreport with
          | [] | [""] -> ()
          | [joutput] ->
            WpReport.export_json stats ~joutput () ;
          | [jinput;joutput] ->
            WpReport.export_json stats ~jinput ~joutput () ;
          | _ ->
            Wp_parameters.error "Invalid format for option -wp-report-json"
        end ;
        List.iter (WpReport.export stats) reports ;
      end ;
    if Wp_parameters.MemoryContext.get () then
      wp_warn_memory_context model
  end

(* ------------------------------------------------------------------------ *)
(* ---  Wp Results                                                      --- *)
(* ------------------------------------------------------------------------ *)

let pp_warnings fmt wpo =
  let ws = Wpo.warnings wpo in
  if ws <> [] then
    let n = List.length ws in
    let s = List.exists (fun w -> w.Warning.severe) ws in
    begin
      match s , n with
      | true , 1 -> Format.fprintf fmt " (Degenerated)"
      | true , _ -> Format.fprintf fmt " (Degenerated, %d warnings)" n
      | false , 1 -> Format.fprintf fmt " (Stronger)"
      | false , _ -> Format.fprintf fmt " (Stronger, %d warnings)" n
    end

(* ------------------------------------------------------------------------ *)
(* ---  Prover Stats                                                    --- *)
(* ------------------------------------------------------------------------ *)

let do_wpo_display goal =
  let result = if Wpo.is_trivial goal then "trivial" else "not tried" in
  Wp_parameters.feedback "Goal %s : %s" (Wpo.get_gid goal) result

module PM =
  Map.Make(struct
    type t = VCS.prover
    let compare = VCS.cmp_prover
  end)

type pstat = {
  mutable proved : int ;
  mutable unknown : int ;
  mutable interrupted : int ;
  mutable incache : int ;
  mutable failed : int ;
  mutable n_time : int ;   (* nbr of measured times *)
  mutable a_time : float ; (* sum of measured times *)
  mutable u_time : float ; (* max time *)
  mutable d_time : float ; (* min time *)
  mutable steps : int ;
}

module GOALS = Wpo.S.Set

let scheduled = ref 0
let exercised = ref 0
let session = ref GOALS.empty
let provers = ref PM.empty

let clear_scheduled () =
  begin
    scheduled := 0 ;
    exercised := 0 ;
    session := GOALS.empty ;
    provers := PM.empty ;
    CfgInfos.trivial_terminates := 0 ;
    WpReached.unreachable_proved := 0 ;
    WpReached.unreachable_failed := 0 ;
  end

let get_pstat p =
  try PM.find p !provers with Not_found ->
    let s = {
      proved = 0 ;
      unknown = 0 ;
      interrupted = 0 ;
      failed = 0 ;
      steps = 0 ;
      incache = 0 ;
      n_time = 0 ;
      a_time = 0.0 ;
      u_time = 0.0 ;
      d_time = max_float ;
    } in provers := PM.add p s !provers ; s

let add_step s n =
  if n > s.steps then s.steps <- n

let add_time s t =
  if t > 0.0 then
    begin
      s.n_time <- succ s.n_time ;
      s.a_time <- t +. s.a_time ;
      if t < s.d_time then s.d_time <- t ;
      if t > s.u_time then s.u_time <- t ;
    end

let do_list_scheduled goals =
  Bag.iter
    (fun goal ->
       begin
         incr scheduled ;
         session := GOALS.add goal !session ;
       end)
    goals ;
  match !scheduled with
  | 0 -> Wp_parameters.warning ~current:false "No goal generated"
  | 1 -> Wp_parameters.feedback "1 goal scheduled"
  | n -> Wp_parameters.feedback "%d goals scheduled" n

let dkey_prover = Wp_parameters.register_category "prover"

let do_wpo_start goal =
  begin
    incr exercised ;
    if Wp_parameters.has_dkey dkey_prover then
      Wp_parameters.feedback "[Qed] Goal %s preprocessing" (Wpo.get_gid goal) ;
  end

let do_wpo_wait () =
  Wp_parameters.feedback ~ontty:`Transient "[wp] Waiting provers..."

let do_progress goal msg =
  begin
    if !scheduled > 0 then
      let pp = int_of_float (100.0 *. float !exercised /. float !scheduled) in
      let pp = max 0 (min 100 pp) in
      Wp_parameters.feedback ~ontty:`Transient "[%02d%%] %s (%s)"
        pp goal.Wpo.po_sid msg ;
  end

(* ------------------------------------------------------------------------ *)
(* ---  Caching                                                         --- *)
(* ------------------------------------------------------------------------ *)

let do_report_cache_usage mode =
  if !exercised > 0 &&
     not (Wp_parameters.has_dkey VCS.dkey_shell)
  then
    let hits = Cache.get_hits () in
    let miss = Cache.get_miss () in
    if hits <= 0 && miss <= 0 then
      Wp_parameters.result "[Cache] not used"
    else
      Wp_parameters.result "[Cache]%t"
        begin fun fmt ->
          let sep = ref " " in
          let pp_cache fmt n job =
            if n > 0 then
              ( Format.fprintf fmt "%s%s:%d" !sep job n ; sep := ", " ) in
          match mode with
          | Cache.NoCache -> ()
          | Cache.Replay ->
            pp_cache fmt hits "found" ;
            pp_cache fmt miss "missed" ;
            Format.pp_print_newline fmt () ;
          | Cache.Offline ->
            pp_cache fmt hits "found" ;
            pp_cache fmt miss "failed" ;
            Format.pp_print_newline fmt () ;
          | Cache.Update | Cache.Cleanup ->
            pp_cache fmt hits "found" ;
            pp_cache fmt miss "updated" ;
            Format.pp_print_newline fmt () ;
          | Cache.Rebuild ->
            pp_cache fmt hits "replaced" ;
            pp_cache fmt miss "updated" ;
            Format.pp_print_newline fmt () ;
        end

(* -------------------------------------------------------------------------- *)
(* --- Prover Results                                                     --- *)
(* -------------------------------------------------------------------------- *)

let do_wpo_stat goal prover res =
  let s = get_pstat prover in
  let open VCS in
  if res.cached then s.incache <- succ s.incache ;
  let smoke = Wpo.is_smoke_test goal in
  let verdict = VCS.verdict ~smoke res in
  match verdict with
  | NoResult | Computing _ | Unknown ->
    s.unknown <- succ s.unknown
  | Stepout | Timeout ->
    s.interrupted <- succ s.interrupted
  | Failed | Invalid ->
    s.failed <- succ s.failed
  | Valid ->
    s.proved <- succ s.proved ;
    add_step s res.prover_steps ;
    add_time s res.prover_time ;
    if prover <> Qed then
      add_time (get_pstat Qed) res.solver_time

let do_wpo_result goal prover res =
  if VCS.is_verdict res then
    begin
      if prover = VCS.Qed then do_progress goal "Qed" ;
      do_wpo_stat goal prover res ;
    end

let results g =
  List.filter
    (fun (_,r) -> VCS.is_verdict r)
    (Wpo.get_results g)

let do_wpo_failed goal =
  let updating = Cache.is_updating () in
  match results goal with
  | [p,r] ->
    Wp_parameters.result "[%a] Goal %s : %t%a"
      VCS.pp_prover p (Wpo.get_gid goal)
      (VCS.pp_result_qualif ~updating p r) pp_warnings goal
  | pres ->
    Wp_parameters.result "[Failed] Goal %s%t" (Wpo.get_gid goal)
      begin fun fmt ->
        pp_warnings fmt goal ;
        List.iter
          (fun (p,r) ->
             Format.fprintf fmt "@\n%8s: @[<hv>%t@]"
               (VCS.title_of_prover p)
               (VCS.pp_result_qualif ~updating p r)
          ) pres ;
      end

let do_wpo_smoke status goal =
  Wp_parameters.result "[%s] Smoke-test %s%t"
    (match status with
     | `Failed -> "Failed"
     | `Passed -> "Passed"
     | `Unknown -> "Partial")
    (Wpo.get_gid goal)
    begin fun fmt ->
      pp_warnings fmt goal ;
      let updating = Cache.is_updating () in
      List.iter
        (fun (p,r) ->
           Format.fprintf fmt "@\n%8s: @[<hv>%t@]"
             (VCS.title_of_prover p)
             (VCS.pp_result_qualif ~updating p r)
        ) (results goal) ;
    end

let do_wpo_success goal s =
  if Wp_parameters.Generate.get () then
    match s with
    | None -> ()
    | Some prover ->
      Wp_parameters.feedback ~ontty:`Silent
        "[%a] Goal %s : Valid" VCS.pp_prover prover (Wpo.get_gid goal)
  else
  if Wpo.is_smoke_test goal then
    begin match s with
      | None ->
        Wp_parameters.feedback ~ontty:`Silent
          "[Passed] Smoke-test %s" (Wpo.get_gid goal)
      | Some _ ->
        let status,target = Wpo.get_proof goal in
        do_wpo_smoke status goal ;
        if status = `Failed then
          let source = fst (Property.location target) in
          Wp_parameters.warning ~source "Failed smoke-test"
    end
  else
    begin match s with
      | None -> do_wpo_failed goal
      | Some (VCS.Tactical as script) ->
        Wp_parameters.feedback ~ontty:`Silent
          "[%a] Goal %s : Valid"
          VCS.pp_prover script (Wpo.get_gid goal)
      | Some prover ->
        let result = Wpo.get_result goal prover in
        let updating = Cache.is_updating () in
        Wp_parameters.feedback ~ontty:`Silent
          "[%a] Goal %s : %t"
          VCS.pp_prover prover (Wpo.get_gid goal)
          (VCS.pp_result_qualif ~updating prover result)
    end

let do_report_time fmt s =
  begin
    if s.n_time > 0 &&
       s.u_time > Rformat.epsilon &&
       not (Wp_parameters.has_dkey VCS.dkey_shell)
    then
      let mean = s.a_time /. float s.n_time in
      let epsilon = 0.05 *. mean in
      let delta = s.u_time -. s.d_time in
      if delta < epsilon then
        Format.fprintf fmt " (%a)" Rformat.pp_time mean
      else
        let middle = (s.u_time +. s.d_time) *. 0.5 in
        if abs_float (middle -. mean) < epsilon then
          Format.fprintf fmt " (%a-%a)"
            Rformat.pp_time s.d_time
            Rformat.pp_time s.u_time
        else
          Format.fprintf fmt " (%a-%a-%a)"
            Rformat.pp_time s.d_time
            Rformat.pp_time mean
            Rformat.pp_time s.u_time
  end

let do_report_steps fmt s =
  begin
    if s.steps > 0 &&
       not (Wp_parameters.has_dkey VCS.dkey_shell)
    then
      Format.fprintf fmt " (%d)" s.steps ;
  end

let do_report_stopped fmt s =
  if Wp_parameters.has_dkey VCS.dkey_shell then
    begin
      let n = s.interrupted + s.unknown in
      if n > 0 then
        Format.fprintf fmt " (unsuccess: %d)" n ;
    end
  else
    begin
      if s.interrupted > 0 then
        Format.fprintf fmt " (interrupted: %d)" s.interrupted ;
      if s.unknown > 0 then
        Format.fprintf fmt " (unknown: %d)" s.unknown ;
      if s.incache > 0 then
        Format.fprintf fmt " (cached: %d)" s.incache ;
    end

let do_report_prover_stats pp_prover fmt (p,s) =
  begin
    let name = VCS.title_of_prover p in
    Format.fprintf fmt "%a %4d " pp_prover name s.proved ;
    do_report_time fmt s ;
    do_report_steps fmt s ;
    do_report_stopped fmt s ;
    if s.failed > 0 then
      Format.fprintf fmt " (failed: %d)" s.failed ;
    Format.fprintf fmt "@\n" ;
  end

let do_report_scheduled () =
  if Wp_parameters.Generate.get () then
    let plural = if !exercised > 1 then "s" else "" in
    Wp_parameters.result "%d goal%s generated" !exercised plural
  else
    let total =
      !scheduled +
      !WpReached.unreachable_failed +
      !WpReached.unreachable_proved +
      !CfgInfos.trivial_terminates in
    if total > 0 then
      begin
        let passed =
          !WpReached.unreachable_proved + !CfgInfos.trivial_terminates
        in
        let passed = GOALS.fold
            (fun g n ->
               if Wpo.is_passed g then succ n else n
            ) !session passed in
        let mode = Cache.get_mode () in
        if mode <> Cache.NoCache then do_report_cache_usage mode ;
        Wp_parameters.result "%t"
          begin fun fmt ->
            Format.fprintf fmt "Proved goals: %4d / %d@\n" passed total ;
            Pretty_utils.pp_items
              ~min:12 ~align:`Left
              ~title:(fun (prover,_) -> VCS.title_of_prover prover)
              ~iter:(fun f -> PM.iter (fun p s -> f (p,s)) !provers)
              ~pp_title:(fun fmt a -> Format.fprintf fmt "%s:" a)
              ~pp_item:do_report_prover_stats fmt ;
          end ;
      end

let do_list_scheduled_result () =
  begin
    do_report_scheduled () ;
    clear_scheduled () ;
  end

(* ------------------------------------------------------------------------ *)
(* ---  Proving                                                         --- *)
(* ------------------------------------------------------------------------ *)

type script = {
  mutable tactical : bool ;
  mutable update : bool ;
  mutable on_stdout : bool ;
  mutable depth : int ;
  mutable width : int ;
  mutable backtrack : int ;
  mutable auto : Strategy.heuristic list ;
  mutable provers : (VCS.mode * VCS.prover) list ;
}

let spawn_wp_proofs ~script goals =
  if script.tactical || script.provers<>[] then
    begin
      let server = ProverTask.server () in
      ignore (Wp_parameters.Share.get_dir "."); (* To prevent further errors *)
      Bag.iter
        (fun goal ->
           if  script.tactical
            && not (Wpo.is_trivial goal)
            && (script.auto <> [] || ProofSession.exists goal)
           then
             ProverScript.spawn
               ~failed:false
               ~auto:script.auto
               ~depth:script.depth
               ~width:script.width
               ~backtrack:script.backtrack
               ~provers:(List.map snd script.provers)
               ~start:do_wpo_start
               ~progress:do_progress
               ~result:do_wpo_result
               ~success:do_wpo_success
               goal
           else
             Prover.spawn goal
               ~delayed:false
               ~start:do_wpo_start
               ~progress:do_progress
               ~result:do_wpo_result
               ~success:do_wpo_success
               script.provers
        ) goals ;
      Task.on_server_wait server do_wpo_wait ;
      Task.launch server
    end

let get_prover_names () =
  match Wp_parameters.Provers.get () with [] -> [ "alt-ergo" ] | pnames -> pnames

let env_script_update () =
  try Sys.getenv "FRAMAC_WP_SCRIPT" = "update"
  with Not_found -> false

let compute_provers ~mode ~script =
  script.provers <- List.fold_right
      begin fun pname prvs ->
        match VCS.parse_prover pname with
        | None -> prvs
        | Some VCS.Tactical ->
          script.tactical <- true ;
          if pname = "tip" || env_script_update () then
            script.update <- true ;
          prvs
        | Some prover ->
          let pmode = if VCS.is_auto prover then VCS.Batch else mode in
          (pmode , prover) :: prvs
      end (get_prover_names ()) []

let dump_strategies =
  let once = ref true in
  fun () ->
    if !once then
      ( once := false ;
        Wp_parameters.result "Registered strategies for -wp-auto:%t"
          (fun fmt ->
             Strategy.iter (fun h ->
                 Format.fprintf fmt "@\n  '%s': %s" h#id h#title
               )))

let default_script_mode () = {
  tactical = false ; update=false ; on_stdout = false ; provers = [] ;
  depth=0 ; width = 0 ; auto=[] ; backtrack = 0 ;
}

let compute_auto ~script =
  script.auto <- [] ;
  script.width <- Wp_parameters.AutoWidth.get () ;
  script.depth <- Wp_parameters.AutoDepth.get () ;
  script.backtrack <- max 0 (Wp_parameters.BackTrack.get ()) ;
  let auto = Wp_parameters.Auto.get () in
  if script.depth <= 0 || script.width <= 0 then
    ( if auto <> [] then
        Wp_parameters.feedback
          "Auto-search deactivated because of 0-depth or 0-width" )
  else
    begin
      List.iter
        (fun id ->
           if id = "?" then dump_strategies ()
           else
             try script.auto <- Strategy.lookup ~id :: script.auto
             with Not_found ->
               Wp_parameters.error ~current:false
                 "Strategy -wp-auto '%s' unknown (ignored)." id
        ) auto ;
      script.auto <- List.rev script.auto ;
      if script.auto <> [] then script.tactical <- true ;
    end

type session_scripts = {
  updated: (Wpo.t * string * Json.t) list;
  incomplete: (Wpo.t * string * Json.t) list;
  removed: (Wpo.t * string) list;
}

let do_collect_session goals =
  let updated = ref [] in
  let incomplete = ref [] in
  let removed = ref [] in
  let file goal =
    Format.asprintf "%a"
      ProofSession.pp_file @@ ProofSession.filename ~force:false goal
  in
  Bag.iter
    begin fun goal ->
      let results = Wpo.get_results goal in
      let autoproof (p,r) =
        (p=VCS.Qed) || (VCS.is_auto p && VCS.is_valid r && VCS.autofit r) in
      if List.exists autoproof results then
        begin
          if ProofSession.exists goal then
            begin
              let file = file goal in
              removed := (goal, file) :: !removed
            end
        end
      else
        let scripts = ProofEngine.script (ProofEngine.proof ~main:goal) in
        if scripts <> [] then
          begin
            let keep = function
              | ProofScript.Prover(p,r) -> VCS.is_auto p && VCS.is_valid r
              | ProofScript.Tactic(n,_,_) -> n=0
              | ProofScript.Error _ -> false in
            let strategy = List.filter keep scripts in
            if strategy <> [] then
              begin
                let file = file goal in
                let json = ProofScript.encode strategy in
                updated := (goal, file, json) :: !updated
              end
            else
            if not (ProofSession.exists goal) then
              begin
                let file = file goal in
                let json = ProofScript.encode scripts in
                incomplete := (goal, file, json) :: !incomplete
              end
          end
    end goals ;
  { updated = !updated ;
    incomplete = !incomplete ;
    removed = !removed ; }

let do_update_session script session =
  let stdout = script.on_stdout in
  List.iter
    begin fun (g, _, s) ->
      (* we always mark existing scripts *)
      ProofSession.mark g ;
      if script.update then ProofSession.save ~stdout g s
    end
    session.updated ;
  List.iter
    begin fun (g, _, s) ->
      (* we mark new incomplete scripts only if we save such files *)
      if script.update then
        (ProofSession.mark g ; ProofSession.save ~stdout g s)
    end
    session.incomplete ;
  List.iter (fun (g, _) -> ProofSession.remove g) session.removed ;
  ()

let do_show_session updated_session session =
  let show enabled kind dkey file =
    if enabled then
      Wp_parameters.result ~dkey "[%s] %a" kind ProofSession.pp_file file
  in
  (* Note: we display new (in)valid scripts only when updating *)
  List.iter
    (fun (_,f,_) -> show updated_session "UPDATED" dkey_script_updated f)
    session.updated ;
  List.iter
    (fun (_,f,_) -> show updated_session "INCOMPLETE" dkey_script_incomplete f)
    session.incomplete ;
  let txt_removed = if updated_session then "REMOVED" else "UNUSED" in
  List.iter
    (fun (_,f) -> show true txt_removed dkey_script_removed f)
    session.removed ;

  let r = List.length session.removed in
  let u = List.length session.updated in
  let f = List.length session.incomplete in

  (* Note: we display new (in)valid scripts only when updating *)
  if (updated_session && (f > 0 || u > 0)) || r > 0 then
    let updated_s =
      let s = if u > 1 then "s" else "" in
      if u = 0 || (not updated_session) then ""
      else Format.asprintf "\n - %d new valid script%s" u s
    in
    let invalid_s =
      let s = if f > 1 then "s" else "" in
      if f = 0 || (not updated_session) then ""
      else Format.asprintf "\n - %d new script%s to complete" f s
    in
    let removed_s =
      let s = if r > 1 then "s" else "" in
      let txt_removed = String.lowercase_ascii txt_removed in
      if r = 0 then ""
      else Format.asprintf "\n - %d script%s %s (now automated)" r s txt_removed
    in
    Wp_parameters.result
      "%s%s%s%s"
      (if updated_session then "Updated session" else "Session can be updated")
      removed_s updated_s invalid_s

let do_session ~script goals =
  let session = do_collect_session goals in
  do_update_session script session ;
  do_show_session script.update session

let do_wp_proofs ?provers ?tip (goals : Wpo.t Bag.t) =
  let script = default_script_mode () in
  let mode = VCS.parse_mode (Wp_parameters.Interactive.get ()) in
  compute_provers ~mode ~script ;
  compute_auto ~script ;
  begin match provers with None -> () | Some prvs ->
    script.provers <- List.map (fun dp -> VCS.Batch , VCS.Why3 dp) prvs
  end ;
  begin match tip with None -> () | Some tip ->
    script.tactical <- tip ;
    script.update <- tip ;
  end ;
  begin
    script.on_stdout <- Wp_parameters.ScriptOnStdout.get ();
  end ;
  let spawned = script.tactical || script.provers <> [] in
  begin
    if spawned then do_list_scheduled goals ;
    spawn_wp_proofs ~script goals ;
    if spawned then
      begin
        do_list_scheduled_result () ;
        do_session ~script goals ;
      end
    else if not (Wp_parameters.Print.get ()) then
      Bag.iter do_wpo_display goals
  end

(* registered at frama-c (normal) exit *)
let do_cache_cleanup () =
  begin
    Cache.cleanup_cache () ;
    let removed = Cache.get_removed () in
    if removed > 0 &&
       not (Wp_parameters.has_dkey VCS.dkey_shell)
    then
      Wp_parameters.result "[Cache] removed:%d" removed
  end

(* ------------------------------------------------------------------------ *)
(* ---  Command-line Entry Points                                       --- *)
(* ------------------------------------------------------------------------ *)

let dkey_logicusage = Wp_parameters.register_category "logicusage"
let dkey_refusage = Wp_parameters.register_category "refusage"
let dkey_builtins = Wp_parameters.register_category "builtins"

let cmdline_run () =
  begin
    if Wp_parameters.CachePrint.get () then
      Kernel.feedback "Cache directory: %s" (Cache.get_dir ()) ;
    let fct = Wp_parameters.get_fct () in
    if fct <> Wp_parameters.Fct_none then
      begin
        Wp_parameters.feedback ~ontty:`Feedback "Running WP plugin...";
        let generator = Generator.create () in
        let model = generator#model in
        Ast.compute ();
        Dyncall.compute ();
        if Wp_parameters.RTE.get () then
          WpRTE.generate_all model ;
        if Wp_parameters.has_dkey dkey_logicusage then
          begin
            LogicUsage.compute ();
            LogicUsage.dump ();
          end ;
        if Wp_parameters.has_dkey dkey_refusage then
          begin
            RefUsage.compute ();
            RefUsage.dump ();
          end ;
        let bhv = Wp_parameters.Behaviors.get () in
        let prop = Wp_parameters.Properties.get () in
        (* TODO entry point *)
        if Wp_parameters.has_dkey dkey_builtins then
          begin
            WpContext.on_context (model,WpContext.Global)
              LogicBuiltins.dump ();
          end ;
        WpTarget.compute model ;
        wp_compute_memory_context model ;
        if Wp_parameters.CheckMemoryContext.get () then
          wp_insert_memory_context model ;
        let goals = generator#compute_main ~fct ~bhv ~prop () in
        do_wp_proofs goals ;
        begin
          if fct <> Wp_parameters.Fct_all then
            do_wp_print_for goals
          else
            do_wp_print () ;
        end ;
        do_wp_report model ;
      end
  end

(* ------------------------------------------------------------------------ *)
(* ---  Tracing WP Invocation                                           --- *)
(* ------------------------------------------------------------------------ *)

let pp_wp_parameters fmt =
  begin
    Format.pp_print_string fmt "# frama-c -wp" ;
    if Wp_parameters.RTE.get () then Format.pp_print_string fmt " -wp-rte" ;
    let spec = Wp_parameters.Model.get () in
    if spec <> [] && spec <> ["Typed"] then
      ( let descr = Factory.descr (Factory.parse spec) in
        Format.fprintf fmt " -wp-model '%s'" descr ) ;
    if not (Wp_parameters.Let.get ()) then Format.pp_print_string fmt
        " -wp-no-let" ;
    if Wp_parameters.Let.get () && not (Wp_parameters.Prune.get ())
    then Format.pp_print_string fmt " -wp-no-prune" ;
    if Wp_parameters.Split.get () then Format.pp_print_string fmt " -wp-split" ;
    let tm = Wp_parameters.Timeout.get () in
    if tm <> 10 then Format.fprintf fmt " -wp-timeout %d" tm ;
    let st = Wp_parameters.Steps.get () in
    if st > 0 then Format.fprintf fmt " -wp-steps %d" st ;
    if not (Kernel.SignedOverflow.get ()) then
      Format.pp_print_string fmt " -no-warn-signed-overflow" ;
    if Kernel.UnsignedOverflow.get () then
      Format.pp_print_string fmt " -warn-unsigned-overflow" ;
    if Kernel.SignedDowncast.get () then
      Format.pp_print_string fmt " -warn-signed-downcast" ;
    if Kernel.UnsignedDowncast.get () then
      Format.pp_print_string fmt " -warn-unsigned-downcast" ;
    if not (Wp_parameters.Volatile.get ()) then
      Format.pp_print_string fmt " -wp-no-volatile" ;
    Format.pp_print_string fmt " [...]" ;
    Format.pp_print_newline fmt () ;
  end

let () = Cmdline.run_after_setting_files
    (fun _ ->
       if Wp_parameters.has_dkey VCS.dkey_shell then
         Log.print_on_output pp_wp_parameters)

(* -------------------------------------------------------------------------- *)
(* --- Prover Configuration & Detection                                   --- *)
(* -------------------------------------------------------------------------- *)

let () = Cmdline.run_after_configuring_stage Why3Provers.configure

let do_prover_detect () =
  if not !Fc_config.is_gui && Wp_parameters.Detect.get () then
    let provers = Why3Provers.provers () in
    if provers = [] then
      Wp_parameters.result "No Why3 provers detected."
    else
      let open Why3.Whyconf in
      let shortcuts = get_prover_shortcuts (Why3Provers.config ()) in
      let print_prover_shortcuts_for fmt p =
        Why3.Wstdlib.Mstr.iter
          (fun name p' -> if Prover.equal p p' then
              Format.fprintf fmt "%s|" name)
          shortcuts in
      List.iter
        (fun p ->
           Wp_parameters.result "Prover %10s %-6s [%a%s]"
             p.prover_name p.prover_version
             print_prover_shortcuts_for p
             (Why3Provers.print_wp p)
        ) provers

(* ------------------------------------------------------------------------ *)
(* ---  Main Entry Points                                               --- *)
(* ------------------------------------------------------------------------ *)

let rec try_sequence jobs () = match jobs with
  | [] -> ()
  | head :: tail ->
    Extlib.try_finally ~finally:(try_sequence tail) head ()

let sequence jobs () =
  if Wp_parameters.has_dkey dkey_raised
  then List.iter (fun f -> f ()) jobs
  else try_sequence jobs ()

let prepare_scripts () =
  if Wp_parameters.PrepareScripts.get () then begin
    Wp_parameters.feedback "Prepare" ;
    ProofSession.reset_marks () ;
    Wp_parameters.PrepareScripts.clear ()
  end

let finalize_scripts () =
  if Wp_parameters.FinalizeScripts.get () then begin
    Wp_parameters.feedback "Finalize" ;
    ProofSession.remove_unmarked_files
      ~dry:(Wp_parameters.DryFinalizeScripts.get()) ;
    Wp_parameters.FinalizeScripts.clear ()
  end

let tracelog () =
  let active_keys = Wp_parameters.get_debug_keys () in
  if active_keys <> [] then begin
    let pp_sep fmt () = Format.pp_print_string fmt "," in
    Wp_parameters.(
      debug "Logging keys: %a."
        (Format.pp_print_list ~pp_sep pp_category) active_keys)
  end

let main = sequence [
    (fun () -> Wp_parameters.debug ~dkey:dkey_main "Start WP plugin...@.") ;
    do_prover_detect ;
    prepare_scripts ;
    cmdline_run ;
    tracelog ;
    finalize_scripts ;
    Wp_parameters.reset ;
    (fun () -> Wp_parameters.debug ~dkey:dkey_main "Stop WP plugin...@.") ;
  ]

let () = Cmdline.at_normal_exit do_cache_cleanup
let () = Db.Main.extend main

(* ------------------------------------------------------------------------ *)
