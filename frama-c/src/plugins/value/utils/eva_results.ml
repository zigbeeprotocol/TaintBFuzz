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

open Cil_datatype

(* {2 Termination.} *)

let partition_terminating_instr stmt =
  let ho =
    try Some (Db.Value.AfterTable_By_Callstack.find stmt)
    with Not_found -> None
  in
  match ho with
  | None -> ([], [])
  | Some h ->
    let terminating = ref [] in
    let non_terminating = ref [] in
    let add x xs = xs := x :: !xs in
    Value_types.Callstack.Hashtbl.iter (fun cs state ->
        if Db.Value.is_reachable state
        then add cs terminating
        else add cs non_terminating) h;
    (!terminating, !non_terminating)

let is_non_terminating_instr stmt =
  match partition_terminating_instr stmt with
  | [], _ -> true
  | _, _ -> false


(* {2 Saving and restoring state} *)

type stmt_by_callstack = Cvalue.Model.t Value_types.Callstack.Hashtbl.t

module AlarmsStmt =
  Datatype.Pair_with_collections (Alarms) (Stmt)
    (struct let module_name = "Value.Eva_results.AlarmStmt" end)

type results = {
  main: Kernel_function.t option (** None means multiple functions *);
  before_states: stmt_by_callstack Stmt.Hashtbl.t;
  after_states: stmt_by_callstack Stmt.Hashtbl.t;
  kf_initial_states: stmt_by_callstack Kernel_function.Hashtbl.t;
  kf_callers: Function_calls.t;
  initial_state: Cvalue.Model.t;
  initial_args: Cvalue.V.t list option;
  alarms: Property_status.emitted_status AlarmsStmt.Hashtbl.t;
  statuses: Property_status.emitted_status Property.Hashtbl.t
(** alarms are _not_ present here *);
  (* conditions then/else *)
}

let get_results () =
  let vue = Emitter.get Eva_utils.emitter in
  let main = Some (fst (Globals.entry_point ())) in
  let module CS = Value_types.Callstack in
  let copy_states iter =
    let h = Stmt.Hashtbl.create 128 in
    let copy stmt hstack = Stmt.Hashtbl.add h stmt (CS.Hashtbl.copy hstack) in
    iter copy;
    h
  in
  let before_states = copy_states Db.Value.Table_By_Callstack.iter in
  let after_states = copy_states Db.Value.AfterTable_By_Callstack.iter in
  let kf_initial_states =
    let h = Kernel_function.Hashtbl.create 128 in
    let copy kf =
      match Db.Value.get_initial_state_callstack kf with
      | None -> ()
      | Some hstack ->
        Kernel_function.Hashtbl.add h kf (CS.Hashtbl.copy hstack)
    in
    Globals.Functions.iter copy;
    h
  in
  let kf_callers = Function_calls.get_results () in
  let initial_state = Db.Value.globals_state () in
  let initial_args = Db.Value.fun_get_args () in
  let aux_statuses f_status ip =
    let aux_any_status e status =
      if Emitter.Usable_emitter.equal vue e.Property_status.emitter then
        f_status status
    in
    Property_status.iter_on_statuses aux_any_status ip
  in
  let alarms = AlarmsStmt.Hashtbl.create 128 in
  let aux_alarms _emitter kf stmt ~rank:_ alarm ca =
    let ip = Property.ip_of_code_annot_single kf stmt ca in
    let f_status st = AlarmsStmt.Hashtbl.add alarms (alarm, stmt) st in
    aux_statuses f_status ip
  in
  Alarms.iter aux_alarms;
  let statuses = Property.Hashtbl.create 128 in
  let aux_ip (ip: Property.t) =
    let add () =
      aux_statuses (fun st -> Property.Hashtbl.add statuses ip st) ip
    in
    match ip with
    | Property.IPCodeAnnot {Property.ica_ca} -> begin
        match Alarms.find ica_ca with
        | None -> (* real property *) add ()
        | Some _ -> (* alarm; do not save it here *) ()
      end
    | Property.IPReachable _ ->
      () (* TODO: save them properly, and restore them *)
    | _ -> add ()
  in
  Property_status.iter aux_ip;
  { before_states; after_states; kf_initial_states; kf_callers;
    initial_state; initial_args; alarms; statuses; main }

let set_results results =
  let selection = State_selection.with_dependencies Self.state in
  Project.clear ~selection ();
  (* Those two functions may clear Self.state. Start by them *)
  (* Initial state *)
  Db.Value.globals_set_initial_state results.initial_state;
  (* Initial args *)
  begin match results.initial_args with
    | None -> Db.Value.fun_use_default_args ()
    | Some l -> Db.Value.fun_set_args l
  end;
  (* Pre- and post-states *)
  let aux_states ~after stmt (h:stmt_by_callstack) =
    let aux_callstack callstack state =
      Db.Value.update_callstack_table ~after stmt callstack state;
    in
    Value_types.Callstack.Hashtbl.iter aux_callstack h
  in
  Stmt.Hashtbl.iter (aux_states ~after:false) results.before_states;
  Stmt.Hashtbl.iter (aux_states ~after:true) results.after_states;
  (* Kf initial state *)
  let aux_initial_state _kf h =
    let aux_callstack callstack state =
      Db.Value.merge_initial_state callstack state
    in
    Value_types.Callstack.Hashtbl.iter aux_callstack h
  in
  Kernel_function.Hashtbl.iter aux_initial_state results.kf_initial_states;
  Function_calls.set_results results.kf_callers;
  (* Alarms *)
  let aux_alarms (alarm, stmt) st =
    let ki = Cil_types.Kstmt stmt in
    ignore (Alarms.register Eva_utils.emitter ki ~status:st alarm)
  in
  AlarmsStmt.Hashtbl.iter aux_alarms results.alarms;
  (* Statuses *)
  let aux_statuses ip st =
    Property_status.emit Eva_utils.emitter ~hyps:[] ip st
  in
  Property.Hashtbl.iter aux_statuses results.statuses;
  let b = Parameters.ResultsAll.get () in
  Cvalue_domain.State.Store.register_global_state b
    (`Value Cvalue_domain.State.top);
  Self.set_computation_state Computed;
  Db.Value.mark_as_computed ();
;;

module HExt (H: Hashtbl.S) =
struct

  let map ?(fkey=fun k _v -> k) ?(fvalue = fun _k v -> v) h =
    let h' = H.create (H.length h) in
    let aux cs v = H.add h' (fkey cs v) (fvalue cs v) in
    H.iter aux h;
    h'

  let merge merge h1 h2 =
    let h = H.create (H.length h1 + H.length h2) in
    let aux1 key v =
      let v' =
        try merge key v (H.find h2 key)
        with Not_found -> v
      in
      H.add h key v'
    in
    let aux2 key v =
      if not (H.mem h1 key) then H.add h key v
    in
    H.iter aux1 h1;
    H.iter aux2 h2;
    h

  include H

end

module CallstackH = HExt(Value_types.Callstack.Hashtbl)
module StmtH = HExt(Stmt.Hashtbl)
module KfH = HExt(Kernel_function.Hashtbl)
module PropertyH = HExt(Property.Hashtbl)
module AlarmsStmtH = HExt(AlarmsStmt.Hashtbl)


let change_callstacks f results =
  let change_callstack h =
    let fkey cs _ = f cs in
    CallstackH.map ~fkey h
  in
  let fvalue _key hcs = change_callstack hcs in
  let change_states h = StmtH.map ~fvalue h in
  let change_kf h = KfH.map ~fvalue h in
  { results with
    before_states = change_states results.before_states;
    after_states = change_states results.after_states;
    kf_initial_states = change_kf results.kf_initial_states
  }

let merge r1 r2 =
  let merge_cs _ = CallstackH.merge (fun _ -> Cvalue.Model.join) in
  (* Keep the "most informative" status. This is not what we do usually,
     because here False + Unknown = False, instead of Unknown *)
  let merge_statuses _ s1 s2 =
    let open Property_status in
    match s1, s2 with
    | False_and_reachable, _ | _, False_and_reachable -> False_and_reachable
    | False_if_reachable, _ | _, False_if_reachable -> False_if_reachable
    | Dont_know, _ | _, Dont_know -> Dont_know
    | True, True -> True
  in
  let merge_s_cs = StmtH.merge merge_cs in
  let main = match r1.main, r2.main with
    | None, _ | _, None -> None
    | Some kf1, Some kf2 ->
      if Kernel_function.equal kf1 kf2 then Some kf1 else None
  in
  let before_states = merge_s_cs r1.before_states r2.before_states in
  let after_states = merge_s_cs r1.after_states r2.after_states in
  let kf_initial_states =
    KfH.merge merge_cs r1.kf_initial_states r2.kf_initial_states
  in
  let kf_callers = Function_calls.merge_results r1.kf_callers r2.kf_callers in
  let alarms = AlarmsStmtH.merge merge_statuses r1.alarms r2.alarms in
  let statuses = PropertyH.merge merge_statuses r1.statuses r2.statuses in
  let initial_state = Cvalue.Model.join r1.initial_state r2.initial_state in
  let initial_args =
    match main, r1.initial_args, r2.initial_args with
    | None, _, _ | _, None, _ | _, _, None -> None
    | Some _kf, Some args1, Some args2 ->
      (* same number of arguments : arity of [_kf] *)
      try Some (List.map2 Cvalue.V.join args1 args2)
      with Invalid_argument _ -> None (* should not occur *)
  in
  { main; before_states; after_states; kf_initial_states;
    initial_state; initial_args; alarms; statuses; kf_callers }


(*
Local Variables:
compile-command: "make -C ../../../.."
End:
*)
