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
open Cil_datatype
open Locations

type taint = {
  (* Over-approximation of the memory locations that are tainted due to a data
     dependency. *)
  locs_data: Zone.t;
  (* Over-approximation of the memory locations that are tainted due to a
     control dependency. *)
  locs_control: Zone.t;
  (* Set of assume statements over a tainted expression. This set is needed to
     implement control-dependency: all left-values appearing in statements whose
     evaluation depends on at least one of the assume expressions is to be
     tainted. This set is restricted to statements of the current function. *)
  assume_stmts: Stmt.Set.t;
  (* Whether the current call depends on a tainted assume statement: if true,
     all assignments in the current call should be control tainted. *)
  dependent_call: bool;
}

let dkey = Self.register_category "d-taint"

(* Debug key to also include [assume_stmts] in the output of the
   Frama_C_domain_show_each directive. *)
let dkey_debug = Self.register_category "d-taint-debug"

let wkey = Self.register_warn_category "taint"

module LatticeTaint = struct

  let pp_locs_only fmt t =
    Format.fprintf fmt
      "@[<v 2>Locations (data):@ @[<hov>%a@]@]@\n\
       @[<v 2>Locations (control):@ @[<hov>%a@]@]"
      Zone.pretty t.locs_data
      Zone.pretty t.locs_control

  let pp_state fmt t =
    Format.fprintf fmt
      "@[<v 2>Locations (data):@ @[<hov>%a@]@]@\n\
       @[<v 2>Locations (control):@ @[<hov>%a@]@]@\n\
       @[<v 2>Assume statements:@ @[<hov>%a@]@\n\
       @[<v 2>Dependent call:@ %b@]"
      Zone.pretty t.locs_data
      Zone.pretty t.locs_control
      Stmt.Set.pretty t.assume_stmts
      t.dependent_call

  (* Frama-C "datatype" for type [taint]. *)
  include Datatype.Make_with_collections(struct
      include Datatype.Serializable_undefined

      type t = taint

      let name = "Value.Taint.t"

      let reprs =
        [ { locs_data = List.hd Zone.reprs;
            locs_control = List.hd Zone.reprs;
            assume_stmts = Stmt.Set.empty;
            dependent_call = false; } ]

      let compare t1 t2 =
        let (<?>) c (cmp,x,y) = if c = 0 then cmp x y else c in
        Zone.compare t1.locs_data t2.locs_data
        <?> (Zone.compare, t1.locs_control, t2.locs_control)
        <?> (Stmt.Set.compare, t1.assume_stmts, t2.assume_stmts)
        <?> (Datatype.Bool.compare, t1.dependent_call, t2.dependent_call)

      let equal = Datatype.from_compare

      let pretty fmt t =
        if Self.is_debug_key_enabled dkey_debug
        then pp_state fmt t
        else pp_locs_only fmt t

      let hash t =
        Hashtbl.hash
          (Zone.hash t.locs_data,
           Zone.hash t.locs_control,
           Stmt.Set.hash t.assume_stmts,
           t.dependent_call)

      let copy c = c

    end)

  (* Initial state at the start of the computation: nothing is tainted yet. *)
  let empty = {
    locs_data = Zone.bottom;
    locs_control = Zone.bottom;
    assume_stmts = Stmt.Set.empty;
    dependent_call = false;
  }

  (* Top state: everything is tainted. *)
  let top = {
    locs_data = Zone.top;
    locs_control = Zone.top;
    assume_stmts = Stmt.Set.empty;
    dependent_call = false;
  }

  (* Join: keep pointwise over-approximation. *)
  let join t1 t2 =
    { locs_data = Zone.join t1.locs_data t2.locs_data;
      locs_control = Zone.join t1.locs_control t2.locs_control;
      assume_stmts = Stmt.Set.union t1.assume_stmts t2.assume_stmts;
      dependent_call = t1.dependent_call || t2.dependent_call; }

  (* The memory locations are finite, so the ascending chain property is
     already verified. We simply use a join. *)
  let widen _ _ t1 t2 = join t1 t2

  let narrow t1 t2 =
    `Value {
      locs_data = Zone.narrow t1.locs_data t2.locs_data;
      locs_control = Zone.narrow t1.locs_control t2.locs_control;
      assume_stmts = Stmt.Set.inter t1.assume_stmts t2.assume_stmts;
      dependent_call = t1.dependent_call && t2.dependent_call;
    }

  (* Inclusion testing: pointwise, on locs only. *)
  let is_included t1 t2 =
    Zone.is_included t1.locs_data t2.locs_data &&
    Zone.is_included t1.locs_control t2.locs_control

  (* Intersection testing: pointwise, on locs only. *)
  let intersects t e =
    Zone.intersects t.locs_data e ||
    Zone.intersects t.locs_control e

end


module TransferTaint = struct

  let loc_of_lval valuation lv =
    match valuation.Abstract_domain.find_loc lv with
    | `Value loc -> loc.Eval.loc
    | `Top -> Precise_locs.loc_top

  (* Keeps only active tainted assumes for [stmt]. A tainted assume in [state]
     is considered active on a statement [stmt] whenever there exists a path
     from the tainted assume that not go through [stmt], ie [stmt] is not a
     postdominator for the tainted assume. *)
  let filter_active_tainted_assumes stmt state =
    let kf = Kernel_function.find_englobing_kf stmt in
    let assume_stmts =
      Stmt.Set.filter
        (fun assume_stmt ->
           not (!Db.Postdominators.is_postdominator kf
                  ~opening:assume_stmt ~closing:stmt))
        state.assume_stmts
    in
    { state with assume_stmts }

  (* No update about taint wrt information provided by the other domains. *)
  let update _valuation state = `Value state

  (* Given a lvalue, returns:
     - its memory location (as a zone);
     - its indirect dependencies, i.e. the memory zone its location depends on;
     - whether its location is a singleton. *)
  let compute_zones lval to_loc =
    match lval with
    | Var vi, NoOffset ->
      (* Special case for direct access to variable: do not use [to_loc] here,
         as it will fail for the formal parameters of calls. *)
      let zone = Locations.zone_of_varinfo vi in
      zone, Zone.bottom, true
    | _ ->
      let ploc = to_loc lval in
      let singleton = Precise_locs.cardinal_zero_or_one ploc in
      let lv_zone =
        let loc = Precise_locs.imprecise_location ploc in
        Locations.enumerate_valid_bits Write loc
      in
      let lv_indirect_zone = Eva_utils.indirect_zone_of_lval to_loc lval in
      lv_zone, lv_indirect_zone, singleton

  (* Propagates data- and control-taints for an assignement [lval = exp]. *)
  let assign_aux lval exp to_loc state =
    let lv_zone, lv_indirect_zone, singleton = compute_zones lval to_loc in
    let exp_zone = Eva_utils.zone_of_expr to_loc exp in
    (* [lv] becomes data-tainted if a memory location on which the value of
       [exp] depends on is data-tainted. *)
    let data_tainted = Zone.intersects state.locs_data exp_zone in
    (* [lv] becomes control-tainted if:
       - the current call depends on a tainted assume statements of a caller;
       - the execution of the assignment depends on a tainted assume statement;
       - the value of [exp] is control-tainted;
       - the assigned location depends on tainted values. *)
    let ctrl_tainted =
      state.dependent_call
      || not (Stmt.Set.is_empty state.assume_stmts)
      || Zone.intersects state.locs_control exp_zone
      || LatticeTaint.intersects state lv_indirect_zone
    in
    let update tainted locs =
      if tainted
      then Zone.join locs lv_zone
      else if singleton
      then Zone.diff locs lv_zone
      else locs
    in
    { state with locs_data = update data_tainted state.locs_data;
                 locs_control = update ctrl_tainted state.locs_control; }

  let assign ki lv exp _v valuation state =
    let state =
      match ki with
      | Kglobal ->
        state
      | Kstmt stmt ->
        let state = filter_active_tainted_assumes stmt state in
        let to_loc = loc_of_lval valuation in
        assign_aux lv.Eval.lval exp to_loc state
    in
    `Value state

  let assume stmt exp _b valuation state =
    let state = filter_active_tainted_assumes stmt state in
    (* Add [stmt] as assume statement in [state] as soon as [exp] is tainted. *)
    let to_loc = loc_of_lval valuation in
    let exp_zone = Eva_utils.zone_of_expr to_loc exp in
    let state =
      if not state.dependent_call && LatticeTaint.intersects state exp_zone
      then { state with assume_stmts = Stmt.Set.add stmt state.assume_stmts; }
      else state
    in
    `Value state

  let start_call stmt call _recursion valuation state =
    let state = filter_active_tainted_assumes stmt state in
    let dependent_call =
      state.dependent_call || not (Stmt.Set.is_empty state.assume_stmts)
    in
    let state = { state with assume_stmts = Stmt.Set.empty; dependent_call } in
    let state =
      (* Add tainted actual parameters in [state]. *)
      let to_loc = loc_of_lval valuation in
      List.fold_left
        (fun s { Eval.concrete; formal; _ } ->
           assign_aux (Cil.var formal) concrete to_loc s)
        state
        call.Eval.arguments
    in
    `Value state

  let finalize_call _stmt _call _recursion ~pre ~post =
    (* Recover assume statements from the [pre] abstract state: we assume the
       control-dependency does not extended beyond the function scope. *)
    `Value { post with assume_stmts = pre.assume_stmts;
                       dependent_call = pre.dependent_call; }

  let show_expr valuation state fmt exp =
    let to_loc = loc_of_lval valuation in
    let exp_zone = Eva_utils.zone_of_expr to_loc exp in
    Format.fprintf fmt "%B" (LatticeTaint.intersects state exp_zone)

end


module QueriesTaint = struct

  let top_query = `Value (Cvalue.V.top, None), Alarmset.all

  let extract_expr ~oracle:_ _context _state _expr = top_query
  let extract_lval ~oracle:_ _context _state _lv _typ _locs = top_query

end


module TaintDomain = struct
  type state = taint
  type value = Cvalue.V.t
  type location = Precise_locs.precise_location
  type origin

  include (LatticeTaint: sig
             include Datatype.S_with_collections with type t = state
             include Abstract_domain.Lattice with type state := state
           end)

  include Domain_builder.Complete (LatticeTaint)

  include QueriesTaint

  include (TransferTaint: Abstract_domain.Transfer
           with type state := state
            and type value := value
            and type location := location
            and type origin := origin)

  let log_category = dkey


  (* Logic. *)

  let logic_assign assign location state =
    let exists_tainted_from state deps =
      let single_from_contents dep =
        match dep.Eval.location with
        | None ->
          false
        | Some location ->
          let loc_zone = Precise_locs.enumerate_valid_bits Read location in
          LatticeTaint.intersects state loc_zone
      in
      List.exists single_from_contents deps
    in
    match assign with
    | None
    | Some ((Eval.Frees _ | Allocates _), _) ->
      state
    | Some (Assigns (_, deps), pre_state) ->
      if exists_tainted_from pre_state deps
      then
        let loc_zone = Precise_locs.enumerate_valid_bits Write location in
        { state with locs_data = Zone.join state.locs_data loc_zone }
      else
        state


  (* Scoping and Initialization. *)

  let enter_scope _kind _vars state = state

  let remove_bases bases state =
    let remove = Zone.filter_base (fun b -> not (Base.Hptset.mem b bases)) in
    { state with locs_data = remove state.locs_data;
                 locs_control = remove state.locs_control; }

  let leave_scope _kf vars state =
    let bases = Base.Hptset.of_list (List.map Base.of_varinfo vars) in
    remove_bases bases state


  (* Initial state: initializers are singletons, so we store nothing. *)
  let empty () = LatticeTaint.empty
  let initialize_variable _ _ ~initialized:_ _ state = state
  let initialize_variable_using_type _ _ state  = state


  (* MemExec cache. *)
  let relate _kf _bases _state = Base.SetLattice.empty

  let filter _kf _kind bases state =
    let filter_base = Zone.filter_base (fun b -> Base.Hptset.mem b bases) in
    { state with locs_data = filter_base state.locs_data;
                 locs_control = filter_base state.locs_control;
                 assume_stmts = Stmt.Set.empty; }

  let reuse _kf bases ~current_input ~previous_output =
    let state = remove_bases bases current_input in
    join state previous_output
end

include TaintDomain


(* Registers ACSL builtin predicate \tainted. *)
let () =
  let a_name = "tainted" in
  let a_type = Lvar a_name in
  let builtin_logic_info =
    { bl_name = "\\tainted";
      bl_labels = [];
      bl_params = [ a_name ];
      bl_type = None;
      bl_profile = ["p", a_type];
    }
  in
  Logic_env.add_builtin_logic_function_gen
    Logic_utils.is_same_builtin_profile builtin_logic_info

(* Registers ACSL extension "taint" (statement annotation)
   and "taints" (behavior extension). *)
let () =
  let typer kind context _loc args =
    let open Logic_typing in
    let get_state context =
      match kind with
      | `Pre -> context.pre_state
      | `Post -> context.post_state [Normal]
    in
    let parse context = context.type_term context (get_state context) in
    Ext_terms (List.map (parse context) args)
  in
  Acsl_extension.register_behavior "taints" (typer `Post) false;
  Acsl_extension.register_code_annot_next_stmt "taint" (typer `Pre) false

(* Interpretation of logic by the taint domain, using the cvalue domain. *)
module TaintLogic = struct

  let eval_tlval_zone cvalue_env term =
    let alarm_mode = Eval_terms.Fail in
    try
      let access = Locations.Read in
      Some (Eval_terms.eval_tlval_as_zone_under_over
              ~alarm_mode access cvalue_env term)
    with Eval_terms.LogicEvalError _ -> None

  let eval_term_deps cvalue_env term =
    let alarm_mode = Eval_terms.Fail in
    try
      let result = Eval_terms.eval_term ~alarm_mode cvalue_env term in
      match Logic_label.Map.bindings result.ldeps with
      | [ BuiltinLabel Here, zone ] -> Some (Zone.bottom, zone)
      | _ -> None
    with Eval_terms.LogicEvalError _ -> None

  let eval_term_zone cvalue_env term =
    match eval_tlval_zone cvalue_env term with
    | Some _ as x -> x
    | None -> eval_term_deps cvalue_env term

  let reduce_by_taint_predicate cvalue_env state term positive =
    match eval_term_zone cvalue_env term with
    | None -> state
    | Some (under, _over) ->
      if positive
      then { state with locs_data = Zone.join state.locs_data under }
      else { state with locs_data = Zone.diff state.locs_data under }

  let rec reduce_by_predicate cvalue_env state predicate positive =
    match positive, predicate.pred_content with
    | true, Pand (p1, p2)
    | false, Por (p1, p2) ->
      let state = reduce_by_predicate cvalue_env state p1 positive in
      reduce_by_predicate cvalue_env state p2 positive
    | true, Por (p1, p2)
    | false, Pand (p1, p2) ->
      let state1 = reduce_by_predicate cvalue_env state p1 positive in
      let state2 = reduce_by_predicate cvalue_env state p2 positive in
      join state1 state2
    | _, Pnot p -> reduce_by_predicate cvalue_env state p (not positive)
    | _, Papp ({l_var_info = {lv_name = "\\tainted"}}, _labels, [arg]) ->
      reduce_by_taint_predicate cvalue_env state arg positive
    | _ -> state

  let evaluate_taint_predicate cvalue_env state term =
    match eval_term_zone cvalue_env term with
    | None -> Alarmset.Unknown
    | Some (_under, over) ->
      if Zone.intersects over state.locs_data
      then Alarmset.Unknown
      else Alarmset.False

  let evaluate_predicate cvalue_env state predicate =
    let rec evaluate predicate =
      match predicate.pred_content with
      | Papp ({l_var_info = {lv_name = "\\tainted"}}, _labels, [arg]) ->
        evaluate_taint_predicate cvalue_env state arg
      | Ptrue -> True
      | Pfalse -> False
      | Pand (p1, p2) ->
        begin
          match evaluate p1, evaluate p2 with
          | True, True -> True
          | False, _ | _, False -> False
          | _ -> Unknown
        end
      | Por (p1, p2) ->
        begin
          match evaluate p1, evaluate p2 with
          | True, _ | _, True -> True
          | False, False -> False
          | _ -> Unknown
        end
      | Pnot p ->
        begin
          match evaluate p with
          | True -> False
          | False -> True
          | Unknown -> Unknown
        end
      | _ -> Unknown
    in
    evaluate predicate

  let interpret_taint_extension cvalue_env taint terms =
    let taint_term taint term =
      match eval_tlval_zone cvalue_env term with
      | None ->
        Self.warning ~wkey ~current:true ~once:true
          "Cannot evaluate term %a in taint annotation; ignoring."
          Printer.pp_term term;
        taint
      | Some (under, over) ->
        if not (Zone.equal under over)
        then
          Self.warning ~wkey ~current:true ~once:true
            "Cannot precisely evaluate term %a in taint annotation; \
             over-approximating."
            Printer.pp_term term;
        { taint with locs_data = Zone.join taint.locs_data over }
    in
    List.fold_left taint_term taint terms
end

let interpret_taint_logic
    (module Abstract: Abstractions.S) : (module Abstractions.S) =
  match Abstract.Dom.get Cvalue_domain.State.key, Abstract.Dom.get key with
  | None, _
  | _, None -> (module Abstract)
  | Some get_cvalue_state, Some get_taint_state ->
    let module Dom = struct
      include Abstract.Dom

      let get_states env state =
        let taint = get_taint_state state in
        let get_cvalue state = fst (get_cvalue_state state) in
        let states label = get_cvalue (env.Abstract_domain.states label) in
        let cvalue_env = Abstract_domain.{ env with states = states } in
        Eval_terms.make_env cvalue_env (get_cvalue state), taint

      let evaluate_predicate env state predicate =
        match evaluate_predicate env state predicate with
        | Unknown ->
          let cvalue_env, taint = get_states env state in
          TaintLogic.evaluate_predicate cvalue_env taint predicate
        | x -> x

      let reduce_by_predicate env state predicate positive =
        match reduce_by_predicate env state predicate positive with
        | `Bottom -> `Bottom
        | `Value state ->
          let cvalue_env, taint = get_states env state in
          let taint =
            TaintLogic.reduce_by_predicate cvalue_env taint predicate positive
          in
          `Value (Abstract.Dom.set key taint state)

      let interpret_acsl_extension extension env state =
        if String.equal extension.ext_name "taint"
        || String.equal extension.ext_name "taints"
        then
          match extension.ext_kind with
          | Ext_terms terms ->
            let cvalue_env, taint = get_states env state in
            let taint =
              TaintLogic.interpret_taint_extension cvalue_env taint terms
            in
            Abstract.Dom.set key taint state
          | _ ->
            Self.warning ~wkey ~current:true ~once:true
              "Invalid taint annotation %a; ignoring."
              Printer.pp_extended extension;
            state
        else state
    end
    in
    (module struct
      module Val = Abstract.Val
      module Loc = Abstract.Loc
      module Dom = Dom
    end)

(* Registers the domain. *)
let flag =
  let name = "taint"
  and descr = "Taint analysis"
  and experimental = true
  and abstraction =
    Abstractions.{ values = Single (module Main_values.CVal);
                   domain = Domain (module TaintDomain); }
  in
  Abstractions.register ~name ~descr ~experimental abstraction

let () = Abstractions.register_hook interpret_taint_logic


type taint_error = NotComputed | Irrelevant | LogicError
type taint_ok = Data | Control | None
type taint_result = (taint_ok, taint_error) result

let zone_of_predicate env predicate =
  let logic_deps = Eval_terms.predicate_deps env predicate in
  let deps_list = Option.map Logic_label.Map.bindings logic_deps in
  match deps_list with
  | Some [ BuiltinLabel Here, zone ] -> Ok zone
  | _ -> Error LogicError

let get_predicate = function
  | Property.IPCodeAnnot ica ->
    begin
      match ica.ica_ca.annot_content with
      | AAssert (_, predicate) | AInvariant (_, _, predicate) ->
        Ok predicate.tp_statement
      | _ -> Error Irrelevant
    end
  | IPPropertyInstance { ii_pred = None } -> Error LogicError
  | IPPropertyInstance { ii_pred = Some pred } -> Ok pred.ip_content.tp_statement
  | _ -> Error Irrelevant

let get_stmt ip =
  let kinstr = Property.get_kinstr ip in
  match kinstr with
  | Kglobal -> Error Irrelevant
  | Kstmt stmt -> Ok stmt

let is_tainted_property ip =
  let (let+) = Result.bind in
  if not (Store.is_computed ()) then Error NotComputed else
    let+ stmt = get_stmt ip in
    let+ predicate = get_predicate ip in
    match Store.get_stmt_state ~after:false stmt with
    | `Bottom -> Ok None
    | `Value state ->
      let cvalue = Db.Value.get_stmt_state ~after:false stmt in
      let env = Eval_terms.env_only_here cvalue in
      let+ zone = zone_of_predicate env predicate in
      if Zone.intersects zone state.locs_data
      then Ok Data
      else if Zone.intersects zone state.locs_control
      then Ok Control
      else Ok None
