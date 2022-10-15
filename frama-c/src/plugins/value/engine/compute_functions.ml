(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
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
open Eval

let dkey = Self.register_category "callbacks"

let floats_ok () =
  let u = min_float /. 2. in
  let u = u /. 2. in
  assert (0. < u && u < min_float)

let need_assigns kf =
  let spec = Annotations.funspec ~populate:false kf in
  match Cil.find_default_behavior spec with
  | None -> true
  | Some bhv -> bhv.b_assigns = WritesAny

let options_ok () =
  (* Check that we can parse the values specified for the options that require
     advanced parsing. Just make a query, as this will force the kernel to
     parse them. *)
  let check f = try ignore (f ()) with Not_found -> () in
  check Parameters.SplitReturnFunction.get;
  check Parameters.BuiltinsOverrides.get;
  check Parameters.SlevelFunction.get;
  check Parameters.EqualityCallFunction.get;
  let check_assigns kf =
    if need_assigns kf then
      Self.error "@[no assigns@ specified@ for function '%a',@ for \
                  which@ a builtin@ or the specification@ will be used.@ \
                  Potential unsoundness.@]" Kernel_function.pretty kf
  in
  Parameters.BuiltinsOverrides.iter (fun (kf, _) -> check_assigns kf);
  Parameters.UsePrototype.iter (fun kf -> check_assigns kf)

let plugins_ok () =
  if not (Plugin.is_present "inout") then
    Self.warning
      "The inout plugin is missing: some features are disabled, \
       and the analysis may have degraded precision and performance."

(* Do something tasteless in case the user did not put a spec on functions
   for which he set [-eva-use-spec]:  generate an incorrect one ourselves *)
let generate_specs () =
  let aux kf =
    if need_assigns kf then begin
      let spec = Annotations.funspec ~populate:false kf in
      Self.warning "Generating potentially incorrect assigns \
                    for function '%a' for which option %s is set"
        Kernel_function.pretty kf Parameters.UsePrototype.option_name;
      (* The function populate_spec may emit a warning. Position a loc. *)
      Cil.CurrentLoc.set (Kernel_function.get_location kf);
      ignore (!Annotations.populate_spec_ref kf spec)
    end
  in
  Parameters.UsePrototype.iter aux

let pre_analysis () =
  floats_ok ();
  options_ok ();
  plugins_ok ();
  Split_return.pretty_strategies ();
  generate_specs ();
  Widen.precompute_widen_hints ();
  Builtins.prepare_builtins ();
  Eva_perf.reset ();
  (* We may be resuming Value from a previously crashed analysis. Clear
     degeneration states *)
  Eva_utils.DegenerationPoints.clear ();
  Cvalue.V.clear_garbled_mix ();
  Eva_utils.clear_call_stack ()

let post_analysis_cleanup ~aborted =
  Eva_utils.clear_call_stack ();
  (* Precompute consolidated states if required *)
  if Parameters.JoinResults.get () then
    Db.Value.Table_By_Callstack.iter
      (fun s _ -> ignore (Db.Value.get_stmt_state s));
  if not aborted then
    (* Keep memexec results for users that want to resume the analysis *)
    Mem_exec.cleanup_results ()

let post_analysis () =
  (* Garbled mix must be dumped here -- at least before the call to
     mark_green_and_red -- because fresh ones are created when re-evaluating
     all the alarms, and we get an unpleasant "ghost effect". *)
  Eva_utils.dump_garbled_mix ();
  (* Mark unreachable and RTE statuses. Only do this there, not when the
     analysis was aborted (hence, not in post_cleanup), because the
     propagation is incomplete. Also do not mark unreachable statutes if
     there is an alarm in the initializers (bottom initial state), as we
     would end up marking the alarm as dead. *)
  Eval_annots.mark_unreachable ();
  (* Try to refine the 'Unknown' statuses that have been emitted during
     this analysis. *)
  Eval_annots.mark_green_and_red ();
  Eva_dynamic.RteGen.mark_generated_rte ();
  post_analysis_cleanup ~aborted:false;
  (* Remove redundant alarms *)
  if Parameters.RmAssert.get () then Eva_dynamic.Scope.rm_asserts ()

(* Registers signal handlers for SIGUSR1 and SIGINT to cleanly abort the Eva
   analysis. Returns a function that restores previous signal behaviors after
   the analysis. *)
let register_signal_handler () =
  let warn () =
    Self.warning ~once:true "Stopping analysis at user request@."
  in
  let stop _ = warn (); Iterator.signal_abort () in
  let interrupt _ = warn (); raise Sys.Break in
  let register_handler signal handler =
    match Sys.signal signal (Sys.Signal_handle handler) with
    | previous_behavior -> fun () -> Sys.set_signal signal previous_behavior
    | exception Invalid_argument _ -> fun () -> ()
    (* Ignore: SIGURSR1 is not available on Windows,
       and possibly on other platforms. *)
  in
  let restore_sigusr1 = register_handler Sys.sigusr1 stop in
  let restore_sigint = register_handler Sys.sigint interrupt in
  fun () -> restore_sigusr1 (); restore_sigint ()

module Make (Abstract: Abstractions.Eva) = struct

  module PowersetDomain = Powerset.Make (Abstract.Dom)

  module Transfer = Transfer_stmt.Make (Abstract)
  module Logic = Transfer_logic.Make (Abstract.Dom) (PowersetDomain)
  module Spec = Transfer_specification.Make (Abstract) (PowersetDomain) (Logic)
  module Init = Initialization.Make (Abstract.Dom) (Abstract.Eval) (Transfer)

  module Computer =
    Iterator.Computer
      (Abstract) (PowersetDomain) (Transfer) (Init) (Logic) (Spec)

  let initial_state = Init.initial_state

  let get_cval =
    match Abstract.Val.get Main_values.CVal.key with
    | None -> fun _ -> assert false
    | Some get -> fun value -> get value

  let get_ploc =
    match Abstract.Loc.get Main_locations.PLoc.key with
    | None -> fun _ -> assert false
    | Some get -> fun location -> get location

  (* ----- Mem Exec cache --------------------------------------------------- *)

  module MemExec = Mem_exec.Make (Abstract.Val) (Abstract.Dom)

  let compute_and_cache_call compute kinstr call init_state =
    let args =
      List.map (fun {avalue} -> Eval.value_assigned avalue) call.arguments
    in
    match MemExec.reuse_previous_call call.kf init_state args with
    | None ->
      let call_result = compute kinstr call init_state in
      let () =
        if call_result.Transfer.cacheable = Eval.Cacheable
        then
          let final_states = call_result.Transfer.states in
          MemExec.store_computed_call call.kf init_state args final_states
      in
      call_result
    | Some (states, i) ->
      let stack = Eva_utils.call_stack () in
      let cvalue = Abstract.Dom.get_cvalue_or_top init_state in
      Db.Value.Call_Type_Value_Callbacks.apply (`Memexec, cvalue, stack);
      (* Evaluate the preconditions of kf, to update the statuses
         at this call. *)
      let spec = Annotations.funspec call.kf in
      if not (Eva_utils.skip_specifications call.kf) &&
         Eval_annots.has_requires spec
      then begin
        let ab = Logic.create init_state call.kf in
        ignore (Logic.check_fct_preconditions kinstr call.kf ab init_state);
      end;
      if Parameters.ValShowProgress.get () then begin
        Self.feedback ~current:true
          "Reusing old results for call to %a" Kernel_function.pretty call.kf;
        Self.debug ~dkey
          "calling Record_Value_New callbacks on saved previous result";
      end;
      Db.Value.Record_Value_Callbacks_New.apply (stack, Value_types.Reuse i);
      (* call can be cached since it was cached once *)
      Transfer.{states; cacheable = Cacheable; builtin=false}

  (* ----- Body or specification analysis ----------------------------------- *)

  (* Interprets a [call] at callsite [kinstr] in the state [state] by analyzing
     the body of the called function. *)
  let compute_using_body fundec ~save_results kinstr call state =
    let result = Computer.compute ~save_results call.kf kinstr state in
    Summary.FunctionStats.recompute fundec;
    result

  (* Interprets a [call] at callsite [kinstr] in the state [state] by using the
     specification of the called function. *)
  let compute_using_spec spec kinstr call state =
    if Parameters.InterpreterMode.get ()
    then Self.abort "Library function call. Stopping.";
    Self.feedback ~once:true
      "@[using specification for function %a@]" Kernel_function.pretty call.kf;
    let vi = Kernel_function.get_vi call.kf in
    if Cil.is_in_libc vi.vattr then
      Library_functions.warn_unsupported_spec vi.vorig_name;
    Spec.compute_using_specification ~warn:true kinstr call spec state,
    Eval.Cacheable

  (* Interprets a [call] at callsite [kinstr] in state [state], using its
     specification or body according to [target]. If [-eva-show-progress] is
     true, the callstack and additional information are printed. *)
  let compute_using_spec_or_body target kinstr call state =
    let global = match kinstr with Kglobal -> true | _ -> false in
    let pp = not global && Parameters.ValShowProgress.get () in
    let call_stack = Eva_utils.call_stack () in
    if pp then
      Self.feedback
        "@[computing for function %a.@\nCalled from %a.@]"
        Value_types.Callstack.pretty_short call_stack
        Cil_datatype.Location.pretty (Cil_datatype.Kinstr.loc kinstr);
    let cvalue_state = Abstract.Dom.get_cvalue_or_top state in
    let compute, kind =
      match target with
      | `Def (fundec, save_results) ->
        compute_using_body fundec ~save_results, `Def
      | `Spec funspec ->
        compute_using_spec funspec, `Spec funspec
    in
    Db.Value.Call_Type_Value_Callbacks.apply (kind, cvalue_state, call_stack);
    let resulting_states, cacheable = compute kinstr call state in
    if pp then
      Self.feedback
        "Done for function %a" Kernel_function.pretty call.kf;
    Transfer.{ states = resulting_states; cacheable; builtin=false }

  (* ----- Use of cvalue builtins ------------------------------------------- *)

  let get_cvalue_call call =
    let lift_left left = { left with lloc = get_ploc left.lloc } in
    let lift_flagged_value value = { value with v = value.v >>-: get_cval } in
    let lift_assigned = function
      | Assign value -> Assign (get_cval value)
      | Copy (lval, value) -> Copy (lift_left lval, lift_flagged_value value)
    in
    let lift_argument arg = { arg with avalue = lift_assigned arg.avalue } in
    let arguments = List.map lift_argument call.arguments in
    let rest = List.map (fun (e, assgn) -> e, lift_assigned assgn) call.rest in
    { call with arguments; rest }

  let join_states = function
    | [] -> `Bottom
    | (_k,s) :: l  ->
      `Value (List.fold_left Abstract.Dom.join s (List.map snd l))

  (* Interprets a call to [kf] at callsite [kinstr] in the state [state]
     by using a cvalue builtin. *)
  let compute_builtin (name, builtin, cacheable, spec) kinstr call state =
    let kf_name = Kernel_function.get_name call.kf in
    if Parameters.ValShowProgress.get ()
    then
      Self.feedback ~current:true "Call to builtin %s%s"
        name (if kf_name = name then "" else " for function " ^ kf_name);
    (* Do not track garbled mixes created when interpreting the specification,
       as the result of the cvalue builtin will overwrite them. *)
    Locations.Location_Bytes.do_track_garbled_mix false;
    let states =
      Spec.compute_using_specification ~warn:false kinstr call spec state
    in
    Locations.Location_Bytes.do_track_garbled_mix true;
    let final_state = join_states states in
    let cvalue_state = Abstract.Dom.get_cvalue_or_top state in
    match final_state with
    | `Bottom ->
      let cs = Eva_utils.call_stack () in
      Db.Value.Call_Type_Value_Callbacks.apply (`Spec spec, cvalue_state, cs);
      let cacheable = Eval.Cacheable in
      Transfer.{states; cacheable; builtin=true}
    | `Value final_state ->
      let cvalue_call = get_cvalue_call call in
      let post = Abstract.Dom.get_cvalue_or_top final_state in
      let cvalue_states =
        Builtins.apply_builtin builtin cvalue_call ~pre:cvalue_state ~post
      in
      let insert cvalue_state =
        Partition.Key.empty,
        Abstract.Dom.set Cvalue_domain.State.key cvalue_state final_state
      in
      let states = List.map insert cvalue_states in
      Transfer.{states; cacheable; builtin=true}

  (* Uses cvalue builtin only if the cvalue domain is available. Otherwise, only
     use the called function specification. *)
  let compute_builtin =
    if Abstract.Dom.mem Cvalue_domain.State.key
    && Abstract.Val.mem Main_values.CVal.key
    && Abstract.Loc.mem Main_locations.PLoc.key
    then compute_builtin
    else fun (_, _, _, spec) -> compute_using_spec_or_body (`Spec spec)

  (* ----- Call computation ------------------------------------------------- *)

  (* Interprets a [call] at callsite [kinstr] in the state [state],
     using a builtin, the specification or the body of the called function,
     according to [Function_calls.register]. *)
  let compute_call kinstr call recursion state =
    let recursion_depth = Option.map (fun r -> r.depth) recursion in
    let target =
      Function_calls.define_analysis_target ?recursion_depth kinstr call.kf
    in
    match target with
    | `Builtin builtin_info -> compute_builtin builtin_info kinstr call state
    | `Spec _ as spec -> compute_using_spec_or_body spec kinstr call state
    | `Def _ as def ->
      let compute = compute_using_spec_or_body def in
      if Parameters.MemExecAll.get ()
      then compute_and_cache_call compute kinstr call state
      else compute kinstr call state

  let () = Transfer.compute_call_ref := (fun stmt -> compute_call (Kstmt stmt))

  (* ----- Main call -------------------------------------------------------- *)

  let store_initial_state kf init_state =
    Abstract.Dom.Store.register_initial_state (Eva_utils.call_stack ()) init_state;
    let cvalue_state = Abstract.Dom.get_cvalue_or_top init_state in
    Db.Value.Call_Value_Callbacks.apply (cvalue_state, [kf, Kglobal])

  let compute kf init_state =
    let restore_signals = register_signal_handler () in
    let compute () =
      Eva_utils.push_call_stack kf Kglobal;
      store_initial_state kf init_state;
      let call =
        { kf; callstack = []; arguments = []; rest = []; return = None; }
      in
      let final_result = compute_call Kglobal call None init_state in
      let final_states = List.map snd (final_result.Transfer.states) in
      let final_state = PowersetDomain.(final_states |> of_list |> join) in
      Eva_utils.pop_call_stack ();
      Self.feedback "done for function %a" Kernel_function.pretty kf;
      Abstract.Dom.Store.mark_as_computed ();
      Self.(set_computation_state Computed);
      post_analysis ();
      Abstract.Dom.post_analysis final_state;
      Summary.print_summary ();
      restore_signals ()
    in
    let cleanup () =
      Abstract.Dom.Store.mark_as_computed ();
      Self.(set_computation_state Aborted);
      post_analysis_cleanup ~aborted:true
    in
    Eva_utils.protect compute ~cleanup

  let compute_from_entry_point kf ~lib_entry =
    pre_analysis ();
    Self.feedback "Analyzing a%scomplete application starting at %a"
      (if lib_entry then "n in" else " ")
      Kernel_function.pretty kf;
    let initial_state =
      Eva_utils.protect
        (fun () -> Init.initial_state_with_formals ~lib_entry kf)
        ~cleanup:(fun () -> post_analysis_cleanup ~aborted:true)
    in
    match initial_state with
    | `Bottom ->
      Abstract.Dom.Store.mark_as_computed ();
      Self.(set_computation_state Aborted);
      Self.result "Eva not started because globals \
                   initialization is not computable.";
      Eval_annots.mark_invalid_initializers ()
    | `Value init_state ->
      compute kf init_state

  let compute_from_init_state kf init_state =
    pre_analysis ();
    let b = Parameters.ResultsAll.get () in
    Abstract.Dom.Store.register_global_state b (`Value init_state);
    compute kf init_state
end


(*
Local Variables:
compile-command: "make -C ../../../.."
End:
*)
