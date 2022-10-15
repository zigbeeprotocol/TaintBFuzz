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

(* Types *)

type alarm_category =
  | Division_by_zero
  | Memory_access
  | Index_out_of_bound
  | Invalid_shift
  | Overflow
  | Uninitialized
  | Dangling
  | Nan_or_infinite
  | Float_to_int
  | Other

module AlarmCategory =
struct
  type t = alarm_category

  let of_alarm = function
    | Alarms.Division_by_zero _ -> Division_by_zero
    | Memory_access _           -> Memory_access
    | Index_out_of_bound _      -> Index_out_of_bound
    | Invalid_shift _           -> Invalid_shift
    | Overflow _                -> Overflow
    | Uninitialized _           -> Uninitialized
    | Dangling _                -> Dangling
    | Is_nan_or_infinite _
    | Is_nan _                  -> Nan_or_infinite
    | Float_to_int _            -> Float_to_int
    | _                         -> Other

  let id = function
    | Division_by_zero    -> 0
    | Memory_access       -> 1
    | Index_out_of_bound  -> 2
    | Invalid_shift       -> 4
    | Overflow            -> 5
    | Uninitialized       -> 6
    | Dangling            -> 7
    | Nan_or_infinite     -> 8
    | Float_to_int        -> 9
    | Other               -> 10

  let compare c1 c2 = id c1 - id c2
  let equal c1 c2 = id c1 = id c2
  let hash c = id c
end

type coverage =
  { mutable reachable: int;
    mutable dead: int; }

type statuses =
  { mutable valid: int;
    mutable unknown: int;
    mutable invalid: int; }

type events =
  { mutable errors: int;
    mutable warnings: int; }

type alarms = (alarm_category * int) list (* Alarm count for each category *)

type fun_stats =
  { fun_coverage: coverage;
    fun_alarm_count: alarms;
    fun_alarm_statuses: statuses; }

type program_stats =
  { prog_fun_coverage: coverage;
    prog_stmt_coverage: coverage;
    prog_alarms: alarms;
    eva_events: events;
    kernel_events: events;
    alarms_statuses: statuses;
    assertions_statuses: statuses;
    preconds_statuses: statuses; }

module AlarmsStats =
struct
  include Hashtbl.Make (AlarmCategory)

  let get t a = try find t a with Not_found -> 0
  let add t a c = replace t a (get t a + c)
  let incr t a = add t a 1
  let to_list t = fold (fun a c l -> (a,c) :: l) t []
  let add_list t l = List.iter (fun (a,c) -> add t a c) l
end


(* --- Datatypes --- *)

module Coverage = struct
  let make () =
    { reachable = 0;
      dead = 0; }
  let total c = c.reachable + c.dead
  let incr c ~reachable = match reachable with
    | false -> c.dead <- c.dead + 1
    | true -> c.reachable <- c.reachable + 1
  let add c1 c2 =
    c1.reachable <- c1.reachable + c2.reachable;
    c1.dead <- c1.dead + c2.dead
end

module Statuses = struct
  let make () =
    { valid = 0;
      unknown = 0;
      invalid = 0; }
  let total c = c.valid + c.unknown + c.invalid
  let incr c = function
    | Property_status.Dont_know           -> c.unknown <- c.unknown + 1
    | Property_status.True                -> c.valid <- c.valid + 1
    | Property_status.False_if_reachable
    | Property_status.False_and_reachable -> c.invalid <- c.invalid + 1
end

module Events = struct
  let make () =
    { errors = 0;
      warnings = 0; }
  let total c = c.errors + c.warnings
end

(* --- Function stats computation --- *)

let get_status ip =
  let eva_emitter = Eva_utils.emitter in
  let aux_status emitter status acc =
    let emitter = Emitter.Usable_emitter.get emitter.Property_status.emitter in
    if Emitter.equal eva_emitter emitter
    then Some status
    else acc
  in
  Property_status.fold_on_statuses aux_status ip None

let compute_fun_stats fundec =
  let alarms = AlarmsStats.create 13
  and coverage = Coverage.make ()
  and statuses = Statuses.make ()
  in
  let kf = Globals.Functions.get fundec.Cil_types.svar in
  let do_status alarm ip =
    match get_status ip with
    | None -> ()
    | Some status ->
      Statuses.incr statuses status;
      match status with
      | Property_status.True -> ()
      | _ -> AlarmsStats.incr alarms (AlarmCategory.of_alarm alarm)
  in
  let do_annot stmt _emitter annotation =
    match Alarms.find annotation with
    | None -> ()
    | Some alarm ->
      let l = Property.ip_of_code_annot kf stmt annotation in
      List.iter (do_status alarm) l
  in
  let do_stmt stmt =
    let reachable = Db.Value.is_reachable_stmt stmt in
    Coverage.incr coverage ~reachable;
    Annotations.iter_code_annot (do_annot stmt) stmt
  in
  List.iter do_stmt fundec.Cil_types.sallstmts;
  { fun_coverage = coverage;
    fun_alarm_count = AlarmsStats.to_list alarms;
    fun_alarm_statuses = statuses; }


module FunctionStats_Type = Datatype.Make (struct
    include Datatype.Serializable_undefined
    type t = fun_stats
    let name = "Eva.Summary.FunctionStats_Type"
    let reprs = [{
        fun_coverage = Coverage.make ();
        fun_alarm_count = [];
        fun_alarm_statuses = Statuses.make ();
      }]
  end)

module FunctionStats = struct
  include State_builder.Hashtbl
      (Cil_datatype.Fundec.Hashtbl)
      (FunctionStats_Type)
      (struct
        let name = "Eva.Summary.FunctionStats"
        let dependencies = [ Self.state ]
        let size = 17
      end)

  module Hook = Hook.Build (struct
      type t = Cil_types.fundec * fun_stats
    end)

  let compute kf =
    let stats = compute_fun_stats kf in
    Hook.apply (kf,stats);
    stats
  let get kf =
    try Some (find kf)
    with Not_found -> None
  let recompute kf = replace kf (compute kf)
  let register_hook = Hook.extend
end


(* --- Program stats computation --- *)

let consider_function vi =
  vi.Cil_types.vdefined &&
  not (Cil_builtins.is_builtin vi
       || Cil_builtins.is_special_builtin vi.vname
       || Cil.is_in_libc vi.vattr)

let compute_events () =
  let eva = Events.make () and kernel = Events.make () in
  let incr_err entry =
    entry.errors <- entry.errors + 1
  and incr_warn entry =
    entry.warnings <- entry.warnings + 1
  in
  let do_event event =
    let open Log in
    match event.evt_kind, event.evt_plugin with
    | Warning, "eva" when event.evt_category <> Some "alarm" ->
      incr_warn eva
    | Warning, name when name = Log.kernel_label_name ->
      incr_warn kernel
    | Error, "eva" when event.evt_category <> Some "alarm" ->
      incr_err eva
    | Error, name when name = Log.kernel_label_name ->
      incr_warn kernel
    | _ -> ()
  in
  Messages.iter do_event;
  eva, kernel

let compute_statuses ()  =
  let alarms = Statuses.make ()
  and assertions = Statuses.make ()
  and preconds = Statuses.make ()
  in
  let do_property ip =
    let incr stmt statuses =
      if Db.Value.is_reachable_stmt stmt then
        match get_status ip with
        | None -> ()
        | Some status -> Statuses.incr statuses status
    in
    match ip with
    | Property.IPCodeAnnot Property.{ica_ca; ica_stmt} ->
      begin
        match Alarms.find ica_ca with
        | None -> incr ica_stmt assertions
        | Some _alarm -> incr ica_stmt alarms
      end
    | Property.IPPropertyInstance {Property.ii_stmt} ->
      incr ii_stmt preconds
    | _ -> ()
  in
  Property_status.iter do_property;
  alarms, assertions, preconds

let compute_stats () =
  let prog_fun_coverage = Coverage.make ()
  and prog_stmt_coverage = Coverage.make ()
  and prog_alarms = AlarmsStats.create 131
  in
  let do_fun fundec =
    let consider = consider_function fundec.Cil_types.svar in
    match FunctionStats.get fundec with
    | Some fun_stats ->
      AlarmsStats.add_list prog_alarms fun_stats.fun_alarm_count;
      if consider then
        begin
          Coverage.incr prog_fun_coverage ~reachable:true;
          Coverage.add prog_stmt_coverage fun_stats.fun_coverage;
        end
    | None ->
      if consider then Coverage.incr prog_fun_coverage ~reachable:false;
  in
  Globals.Functions.iter_on_fundecs do_fun;
  let alarms_statuses, assertions_statuses, preconds_statuses =
    compute_statuses ()
  and eva_events, kernel_events = compute_events () in
  { prog_fun_coverage;
    prog_stmt_coverage;
    prog_alarms=AlarmsStats.to_list prog_alarms;
    eva_events;
    kernel_events;
    alarms_statuses;
    assertions_statuses;
    preconds_statuses; }


(* --- Printing --- *)

let plural count = if count = 1 then "" else "s"

let print_coverage fmt {prog_fun_coverage=funs; prog_stmt_coverage=stmts} =
  let funs_total = Coverage.total funs
  and stmts_total = Coverage.total stmts in
  if funs_total = 0
  then Format.fprintf fmt "No function to be analyzed.@;"
  else
    Format.fprintf fmt
      "%i function%s analyzed (out of %i): %i%% coverage.@;"
      funs.reachable (plural funs.reachable) funs_total
      (funs.reachable * 100 / funs_total);
  if funs_total > 0 && stmts_total > 0 then
    Format.fprintf fmt
      "In %s, %i statements reached (out of %i): %i%% coverage.@;"
      (if funs.reachable > 1 then "these functions" else "this function")
      stmts.reachable stmts_total
      (stmts.reachable * 100 / stmts_total)

let print_events fmt stats =
  if Events.total stats.eva_events + Events.total stats.kernel_events = 0
  then Format.fprintf fmt "No errors or warnings raised during the analysis.@;"
  else
    let print str e =
      Format.fprintf fmt "  by %-19s  %3i error%s  %3i warning%s@;"
        (str ^ ":") e.errors (plural e.errors) e.warnings (plural e.warnings)
    in
    Format.fprintf fmt
      "Some errors and warnings have been raised during the analysis:@;";
    print "the Eva analyzer" stats.eva_events;
    print "the Frama-C kernel" stats.kernel_events

let print_alarm fmt (category,count) =
  let str, plural, str' = match category with
    | Division_by_zero -> "division", "s", " by zero"
    | Memory_access -> "invalid memory access", "es", ""
    | Index_out_of_bound -> "access", "es", " out of bounds index"
    | Overflow -> "integer overflow", "s", ""
    | Invalid_shift -> "invalid shift", "s", ""
    | Uninitialized -> "access", "es", " to uninitialized left-values"
    | Dangling -> "escaping address", "es", ""
    | Nan_or_infinite -> "nan or infinite floating-point value", "s", ""
    | Float_to_int -> "illegal conversion", "s", " from floating-point to integer"
    | Other -> "other", "s", ""
  in
  Format.fprintf fmt "  %4i %s%s%s@;"
    count str (if count > 1 then plural else "") str'

let print_alarms fmt {prog_alarms; alarms_statuses} =
  let total = Statuses.total alarms_statuses in
  Format.fprintf fmt "%i alarm%s generated by the analysis" total (plural total);
  match prog_alarms with
  | [] | [Other,_] ->
    Format.fprintf fmt ".@;"
  | _many_alarms_categories ->
    let order x1 x2 =
      match x1, x2 with
      | (Other,c1), (Other,c2) -> c2 - c1
      | (Other,_), _ -> 1 (* "Other" at the end *)
      | _, (Other,_) -> -1
      | (a1,c1), (a2,c2) ->
        (* Descending count order *)
        let d = c2 - c1 in
        if d <> 0 then d else AlarmCategory.compare a1 a2
    in
    Format.fprintf fmt ":@;";
    List.iter (print_alarm fmt) (List.sort order prog_alarms);
    let invalid = alarms_statuses.invalid in
    if invalid > 0 then
      Format.fprintf fmt "%i of them %s sure alarm%s (invalid status).@;"
        invalid (if invalid = 1 then "is a" else "are") (plural invalid)

let print_statuses fmt {assertions_statuses; preconds_statuses} =
  let total_assertions = Statuses.total assertions_statuses
  and total_preconds = Statuses.total preconds_statuses in
  let total = total_assertions + total_preconds in
  if total = 0
  then
    Format.fprintf fmt
      "No logical properties have been reached by the analysis.@;"
  else
    let print_line header status total =
      Format.fprintf fmt
        "  %-14s %4d valid  %4d unknown  %4d invalid   %4d total@;"
        header status.valid status.unknown status.invalid total;
    in
    Format.fprintf fmt
      "Evaluation of the logical properties reached by the analysis:@;";
    print_line "Assertions" assertions_statuses total_assertions;
    print_line "Preconditions" preconds_statuses total_preconds;
    let proven = assertions_statuses.valid + preconds_statuses.valid in
    let proven = proven * 100 / total in
    Format.fprintf fmt
      "%i%% of the logical properties reached have been proven.@;" proven

let print_summary fmt =
  let bar = String.make 76 '-' in
  let stats = compute_stats () in
  Format.fprintf fmt "%s@;" bar;
  print_coverage fmt stats;
  Format.fprintf fmt "%s@;" bar;
  print_events fmt stats;
  Format.fprintf fmt "%s@;" bar;
  print_alarms fmt stats;
  Format.fprintf fmt "%s@;" bar;
  print_statuses fmt stats;
  Format.fprintf fmt "%s" bar

let print_summary () =
  let dkey = Self.dkey_summary in
  let header fmt = Format.fprintf fmt " ====== ANALYSIS SUMMARY ======" in
  Self.printf ~header ~dkey ~level:1 "  @[<v>%t@]" print_summary
