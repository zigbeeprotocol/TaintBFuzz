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
open Eval

module type S = sig
  type state
  type value
  type loc
  val assign: state -> kinstr -> lval -> exp -> state or_bottom
  val assume: state -> stmt -> exp -> bool -> state or_bottom
  val call:
    stmt -> lval option -> exp -> exp list -> state ->
    (Partition.key * state) list * Eval.cacheable
  val check_unspecified_sequence:
    stmt ->
    state -> (stmt * lval list * lval list * lval list * stmt ref list) list ->
    unit or_bottom
  val enter_scope: kernel_function -> varinfo list -> state -> state
  type call_result = {
    states: (Partition.key * state) list;
    cacheable: Eval.cacheable;
    builtin: bool;
  }
  val compute_call_ref:
    (stmt -> (loc, value) call -> recursion option -> state -> call_result) ref
end

(* Reference filled in by the callwise-inout callback *)
module InOutCallback =
  State_builder.Option_ref (Inout_type)
    (struct
      let dependencies = [Self.state]
      let name = "Transfer_stmt.InOutCallback"
    end)

let register_callback () =
  Db.Operational_inputs.Record_Inout_Callbacks.extend_once
    (fun (_stack, inout) -> InOutCallback.set inout)

let () = Cmdline.run_after_configuring_stage register_callback

let current_kf_inout = InOutCallback.get_option

(* Should we warn about indeterminate copies in the function [kf] ? *)
let warn_indeterminate kf =
  let params = Parameters.WarnCopyIndeterminate.get () in
  Kernel_function.Set.mem kf params

(* An assignment from a right scalar lvalue is interpreted as a copy when
   indeterminate copies are allowed. Otherwise, such assignments are interpreted
   through the evaluation of the right lvalue, possibly leading to alarms about
   non initialization and dangling pointers. *)
let do_copy_at = function
  | Kglobal -> false
  | Kstmt stmt ->
    try
      let kf = Kernel_function.find_englobing_kf stmt in
      not (warn_indeterminate kf)
    with Not_found -> assert false

(* Warn for call arguments that contain uninitialized/escaping except on
   [Frama_C_show_each] directives or if the user disables these alarms
   on functions whose body is analyzed. *)
let is_determinate kf =
  let name = Kernel_function.get_name kf in
  (warn_indeterminate kf || Function_calls.use_spec_instead_of_definition kf)
  && not (Ast_info.is_frama_c_builtin name)

let subdivide_stmt = Eva_utils.get_subdivision

let subdivide_kinstr = function
  | Kglobal -> Parameters.LinearLevel.get ()
  | Kstmt stmt -> subdivide_stmt stmt

(* Used to disambiguate files for Frama_C_dump_each_file directives. *)
module DumpFileCounters =
  State_builder.Hashtbl (Datatype.String.Hashtbl) (Datatype.Int)
    (struct
      let size = 3
      let dependencies = [ Self.state ]
      let name = "Transfer_stmt.DumpFileCounters"
    end)

module VarHashtbl = Cil_datatype.Varinfo.Hashtbl

let substitution_visitor table = object
  inherit Visitor.frama_c_copy (Project.current ())

  method! vvrbl varinfo =
    match VarHashtbl.find_opt table varinfo with
    | None -> Cil.JustCopy
    | Some vi -> Cil.ChangeTo vi
end

module Make (Abstract: Abstractions.Eva) = struct

  module Value = Abstract.Val
  module Location = Abstract.Loc
  module Domain = Abstract.Dom
  module Eval = Abstract.Eval

  type state = Domain.t
  type value = Value.t
  type loc = Location.location

  (* When using a product of domains, a product of states may have no
     concretization (if the domains have inferred incompatible properties)
     without being bottom (if the inter-reduction between domains are
     insufficient to prove the incompatibility). In such a state, an evaluation
     can lead to bottom without any alarm (the evaluation reveals the
     incompatibility).  We report these cases to the user, as they could also
     reveal a bug in some Eva's abstractions. Note that they should not happen
     when only one domain is enabled. *)

  let notify_unreachability fmt =
    if Domain.log_category = Domain_product.product_category
    then
      Self.feedback ~level:1 ~current:true ~once:true
        "The evaluation of %(%a%)@ led to bottom without alarms:@ at this point \
         the product of states has no possible concretization.@."
        fmt
    else
      Self.warning ~current:true
        "The evaluation of %(%a%)@ led to bottom without alarms:@ at this point \
         the abstract state has no possible concretization,@ which is probably \
         a bug."
        fmt

  let report_unreachability state (result, alarms) fmt =
    if result = `Bottom && Alarmset.is_empty alarms
    then begin
      Self.debug ~current:true ~once:true ~level:1
        ~dkey:Self.dkey_incompatible_states
        "State without concretization: %a" Domain.pretty state;
      notify_unreachability fmt
    end
    else
      Format.ifprintf Format.std_formatter fmt

  (* The three functions below call evaluation functions and notify the user
     if they lead to bottom without alarms. *)

  let evaluate_and_check ?valuation ~subdivnb state expr =
    let res = Eval.evaluate ?valuation ~subdivnb state expr in
    report_unreachability state res "the expression %a" Printer.pp_exp expr;
    res

  let lvaluate_and_check ?valuation ~subdivnb ~for_writing state lval =
    let res = Eval.lvaluate ?valuation ~subdivnb ~for_writing state lval in
    report_unreachability state res "the lvalue %a" Printer.pp_lval lval;
    res

  let copy_lvalue_and_check ?valuation ~subdivnb state lval =
    let res = Eval.copy_lvalue ?valuation ~subdivnb state lval in
    report_unreachability state res "the copy of %a" Printer.pp_lval lval;
    res

  (* ------------------------------------------------------------------------ *)
  (*                               Assignments                                *)
  (* ------------------------------------------------------------------------ *)

  (* Default assignment: evaluates the right expression. *)
  let assign_by_eval ~subdivnb state valuation expr =
    evaluate_and_check ~valuation ~subdivnb state expr
    >>=: fun (valuation, value) ->
    Assign value, valuation

  (* Assignment by copying the value of a right lvalue. *)
  let assign_by_copy ~subdivnb state valuation lval lloc ltyp =
    (* This code about garbled mix is specific to the Cvalue domain.
       Unfortunately, the current API for abstract_domain does not permit
       distinguishing between an evaluation or a copy. *)
    Locations.Location_Bytes.do_track_garbled_mix false;
    let r = copy_lvalue_and_check ~valuation ~subdivnb state lval in
    Locations.Location_Bytes.do_track_garbled_mix true;
    r >>=: fun (valuation, value) ->
    Copy ({lval; lloc; ltyp}, value), valuation

  (* For an initialization, use for_writing:false for the evaluation of
     the left location, as the written variable could be const.  This is only
     useful for local initializations through function calls, as other
     initializations are handled by initialization.ml. *)
  let for_writing kinstr = match kinstr with
    | Kglobal -> false
    | Kstmt stmt -> match stmt.skind with
      | Instr (Local_init _) -> false
      | _ -> true

  (* Find a lvalue hidden under identity casts. This function correctly detects
     bitfields (thanks to [need_cast]) and will never expose the underlying
     field. *)
  let rec find_lval expr = match expr.enode with
    | Lval lv -> Some lv
    | CastE (typ, e) ->
      if Eval_typ.need_cast typ (Cil.typeOf e) then None else find_lval e
    | _ -> None

  (* Emits an alarm if the left and right locations of a struct or union copy
     overlap. *)
  let check_overlap typ (lval, loc) (right_lval, right_loc) =
    if Cil.isStructOrUnionType typ
    then
      let truth = Location.assume_no_overlap ~partial:true loc right_loc in
      let alarm () = Alarms.Overlap (lval, right_lval) in
      Eval.interpret_truth ~alarm (loc, right_loc) truth
    else `Value (loc, right_loc), Alarmset.none

  (* Checks the compatibility between the left and right locations of a copy. *)
  let are_compatible loc right_loc =
    let size1 = Location.size loc
    and size2 = Location.size right_loc in
    Int_Base.equal size1 size2 && not (Int_Base.is_top size1)

  (* Assignment. *)
  let assign_lv_or_ret ~is_ret state kinstr lval expr =
    let for_writing = for_writing kinstr in
    let subdivnb = subdivide_kinstr kinstr in
    let eval, alarms = lvaluate_and_check ~for_writing ~subdivnb state lval in
    Alarmset.emit kinstr alarms;
    match eval with
    | `Bottom ->
      Kernel.warning ~current:true ~once:true
        "@[<v>@[all target addresses were invalid. This path is \
         assumed to be dead.@]%t@]" Eva_utils.pp_callstack;
      `Bottom
    | `Value (valuation, lloc, ltyp) ->
      (* Tries to interpret the assignment as a copy for the returned value
         of a function call, on struct and union types, and when
         -eva-warn-copy-indeterminate is disabled. *)
      let lval_copy =
        if is_ret || Cil.isStructOrUnionType ltyp || do_copy_at kinstr
        then find_lval expr
        else None
      in
      let eval, alarms = match lval_copy with
        | None ->
          assert (not is_ret);
          assign_by_eval ~subdivnb state valuation expr
        | Some right_lval ->
          let for_writing = false in
          (* In case of a copy, checks that the left and right locations are
             compatible and that they do not overlap. *)
          lvaluate_and_check ~for_writing ~subdivnb ~valuation state right_lval
          >>= fun (valuation, rloc, rtyp) ->
          check_overlap ltyp (lval, lloc) (right_lval, rloc)
          >>= fun (lloc, rloc) ->
          if are_compatible lloc rloc
          then assign_by_copy ~subdivnb state valuation right_lval rloc rtyp
          else assign_by_eval ~subdivnb state valuation expr
      in
      if is_ret then assert (Alarmset.is_empty alarms);
      Alarmset.emit kinstr alarms;
      let* assigned, valuation = eval in
      let domain_valuation = Eval.to_domain_valuation valuation in
      let lvalue = { lval; ltyp; lloc } in
      Domain.assign kinstr lvalue expr assigned domain_valuation state

  let assign = assign_lv_or_ret ~is_ret:false
  let assign_ret = assign_lv_or_ret ~is_ret:true

  (* ------------------------------------------------------------------------ *)
  (*                               Assumption                                 *)
  (* ------------------------------------------------------------------------ *)

  (* Assumption. *)
  let assume state stmt expr positive =
    let eval, alarms = Eval.reduce state expr positive in
    (* TODO: check not comparable. *)
    Alarmset.emit (Kstmt stmt) alarms;
    let* valuation = eval in
    Domain.assume stmt expr positive (Eval.to_domain_valuation valuation) state


  (* ------------------------------------------------------------------------ *)
  (*                             Function Calls                               *)
  (* ------------------------------------------------------------------------ *)

  type call_result = {
    states: (Partition.key * state) list;
    cacheable: cacheable;
    builtin: bool;
  }

  (* Forward reference to [Eval_funs.compute_call] *)
  let compute_call_ref :
    (stmt -> (loc, value) call -> recursion option -> state ->
     call_result) ref
    = ref (fun _ -> assert false)

  (* Returns the result of a call, and a boolean that indicates whether a
     builtin has been used to interpret the call. *)
  let process_call stmt call recursion valuation state =
    Eva_utils.push_call_stack call.kf (Kstmt stmt);
    let cleanup () =
      Eva_utils.pop_call_stack ();
      (* Changed by compute_call_ref, called from process_call *)
      Cil.CurrentLoc.set (Cil_datatype.Stmt.loc stmt);
    in
    let process () =
      let domain_valuation = Eval.to_domain_valuation valuation in
      let res =
        (* Process the call according to the domain decision. *)
        match Domain.start_call stmt call recursion domain_valuation state with
        | `Value state ->
          Domain.Store.register_initial_state (Eva_utils.call_stack ()) state;
          !compute_call_ref stmt call recursion state
        | `Bottom ->
          { states = []; cacheable = Cacheable; builtin=false }
      in
      cleanup ();
      res
    in
    Eva_utils.protect process
      ~cleanup:(fun () -> InOutCallback.clear (); cleanup ())

  (* ------------------- Retro propagation on formals ----------------------- *)


  let get_precise_location = Location.get Main_locations.PLoc.key

  (* [is_safe_argument valuation expr] is true iff the expression [expr] could
     not have been written during the last call.
     If the Location module includes precise_locs, and if the inout plugins
     is run callwise, then the function uses the precise_locs of the [valuation]
     and the results of inout. An argument is safe if its dependencies (the
     locations on which its value depends) do not intersect with the zones
     written by the called function.
     If precise_locs or the callwise inout is not available, a syntactic
     criterion is used. See {!Backward_formals.safe_argument}. *)
  let is_safe_argument =
    let default _ expr = Backward_formals.safe_argument expr in
    match get_precise_location with
    | None -> default
    | Some get ->
      fun valuation expr ->
        match InOutCallback.get_option () with
        | None -> default valuation expr
        | Some inout ->
          let find_loc lval =
            match Eval.Valuation.find_loc valuation lval with
            | `Top -> Precise_locs.loc_top
            | `Value record -> get record.loc
          in
          let expr_zone = Eva_utils.zone_of_expr find_loc expr in
          let written_zone = inout.Inout_type.over_outputs_if_termination in
          not (Locations.Zone.intersects expr_zone written_zone)

  (* Removes from the list of arguments of a call the arguments whose concrete
     or formal argument could have been written during the call, as well as
     arguments of non arithmetic or non pointer type. *)
  let filter_safe_arguments valuation call =
    let written_formals = Backward_formals.written_formals call.kf in
    let is_safe argument =
      not (Varinfo.Set.mem argument.formal written_formals)
      && Cil.isArithmeticOrPointerType argument.formal.vtype
      && is_safe_argument valuation argument.concrete
    in
    List.filter is_safe call.arguments

  (* At the end of a call, this function gathers the arguments whose value can
     be reduced at the call site. These are the arguments such that:
     – the formal has not been written during the call, but its value has been
       reduced;
     – no variable of the concrete argument has been written during the call
       (thus the concrete argument is still equal to the formal).
     [state] is the state at the return statement of the called function;
     it is used to evaluate the formals; their values are then compared to the
     ones at the beginning of the call.
     The function returns an association list between the argument that can be
     reduced, and their new (more precise) value.  *)
  let gather_reduced_arguments call valuation state =
    let safe_arguments = filter_safe_arguments valuation call in
    let empty = Eval.Valuation.empty in
    let reduce_one_argument acc argument =
      let* acc = acc in
      let pre_value = match argument.avalue with
        | Assign pre_value -> `Value pre_value
        | Copy (_lv, pre_value) -> pre_value.v
      in
      let lval = Cil.var argument.formal in
      (* We use copy_lvalue instead of evaluate to get the escaping flag:
         if a formal is escaping at the end of the called function, it may
         have been freed, which is not detected as a write. We prevent the
         backward propagation in that case.
         If the call has copied the argument, it may be uninitialized. Thus,
         we also avoid the backward propagation if the formal is uninitialized
         here. This should not happen in the Assign case above. *)
      let* _valuation, post_value =
        fst (Eval.copy_lvalue ~valuation:empty ~subdivnb:0 state lval) in
      if
        Bottom.is_included Value.is_included pre_value post_value.v
        || post_value.escaping || not post_value.initialized
      then `Value acc
      else post_value.v >>-: fun post_value -> (argument, post_value) :: acc
    in
    List.fold_left reduce_one_argument (`Value []) safe_arguments

  (* [reductions] is an association list between expression and value.
     This function reduces the [state] by assuming [expr = value] for each pair
     (expr, value) of [reductions]. *)
  let reduce_arguments reductions state =
    let valuation = `Value Eval.Valuation.empty in
    let reduce_one_argument valuation (argument, post_value) =
      let* valuation = valuation in
      Eval.assume ~valuation state argument.concrete post_value
    in
    let* valuation = List.fold_left reduce_one_argument valuation reductions in
    Domain.update (Eval.to_domain_valuation valuation) state

  (* -------------------- Treat the results of a call ----------------------- *)

  (* Treat the assignment of the return value in the caller: if the function
     has a non-void type, perform the assignment if there is a lvalue at
     the callsite, and in all cases, remove the pseudo-variable from scope. *)
  let treat_return ~kf_callee lv return stmt state =
    match lv, return with
    | None, None -> `Value state
    | None, Some vi_ret -> `Value (Domain.leave_scope kf_callee [vi_ret] state)
    | Some _, None -> assert false
    | Some lval, Some vi_ret ->
      let exp_ret_caller = Eva_utils.lval_to_exp  (Var vi_ret, NoOffset) in
      let+ state = assign_ret state (Kstmt stmt) lval exp_ret_caller in
      Domain.leave_scope kf_callee [vi_ret] state

  (* ---------------------- Make a one function call ------------------------ *)

  (* The variables leaving scope at the end of a call to [kf]:
     the formals, and the locals of the body of kf, if any. *)
  let leaving_vars kf =
    let locals =
      try
        let fundec = Kernel_function.get_definition kf in
        fundec.sbody.blocals
      with Kernel_function.No_Definition -> []
    in
    Kernel_function.get_formals kf @ locals

  (* Do the call to one function. *)
  let do_one_call valuation stmt lv call recursion state =
    let kf_callee = call.kf in
    let pre = state in
    (* Process the call according to the domain decision. *)
    let call_result = process_call stmt call recursion valuation state in
    let leaving_vars = leaving_vars kf_callee in
    (* Do not try to reduce concrete arguments if a builtin was used. *)
    let gather_reduced_arguments =
      if call_result.builtin
      then fun _ _ _ -> `Value []
      else gather_reduced_arguments
    in
    (* Treat each result one by one. *)
    let process state =
      (* Gathers the possible reductions on the value of the concrete arguments
         at the call site, according to the value of the formals at the post
         state of the called function. *)
      let* reductions = gather_reduced_arguments call valuation state in
      (* The formals (and the locals) of the called function leave scope. *)
      let post = Domain.leave_scope kf_callee leaving_vars state in
      let recursion = Option.map Recursion.revert recursion in
      (* Computes the state after the call, from the post state at the end of
         the called function, and the pre state at the call site. *)
      let* state = Domain.finalize_call stmt call recursion ~pre ~post in
      (* Backward propagates the [reductions] on the concrete arguments. *)
      let* state = reduce_arguments reductions state in
      treat_return ~kf_callee lv call.return stmt state
    in
    let states =
      List.fold_left
        (fun acc (k,x) -> Bottom.add_to_list (process x >>-: fun y -> k,y) acc)
        [] call_result.states
    in
    InOutCallback.clear ();
    call_result.cacheable, states


  (* ------------------- Evaluation of the arguments ------------------------ *)

  (* [evaluate_argument ~determinate valuation state expr]
     evaluates the call argument [expr] in the state [state] and the valuation
     [valuation]. Returns the value assigned, and the updated valuation.
     TODO: share more code with [assign]. *)
  let evaluate_actual ~subdivnb ~determinate valuation state expr =
    match expr.enode with
    | Lval lv ->
      lvaluate_and_check ~for_writing:false ~subdivnb ~valuation state lv
      >>= fun (valuation, loc, typ) ->
      if Int_Base.is_top (Location.size loc)
      then
        Self.abort ~current:true
          "Function argument %a has unknown size. Aborting"
          Printer.pp_exp expr;
      if determinate && Cil.isArithmeticOrPointerType (Cil.typeOfLval lv)
      then assign_by_eval ~subdivnb state valuation expr
      else assign_by_copy ~subdivnb state valuation lv loc typ
    | _ -> assign_by_eval ~subdivnb state valuation expr

  (* Evaluates the list of the actual arguments of a call. Returns the list
     of each argument expression associated to its assigned value, and the
     valuation resulting of the evaluations. *)
  let compute_actuals ~subdivnb ~determinate valuation state arguments =
    let process expr acc =
      acc >>= fun (args, valuation) ->
      evaluate_actual ~subdivnb ~determinate valuation state expr >>=:
      fun (assigned, valuation) ->
      (expr, assigned) :: args, valuation
    in
    List.fold_right process arguments (`Value ([], valuation), Alarmset.none)

  (* ------------------------- Make an Eval.call ---------------------------- *)

  (* Create an Eval.call *)
  let create_call kf args =
    let return = Library_functions.get_retres_vi kf in
    let callstack = Eva_utils.call_stack () in
    let arguments, rest =
      let formals = Kernel_function.get_formals kf in
      let rec format_arguments acc args formals = match args, formals with
        | _, [] -> acc, args
        | [], _ -> assert false
        | (concrete, avalue) :: args, formal :: formals ->
          let argument = { formal ; concrete; avalue } in
          format_arguments (argument :: acc)  args formals
      in
      let arguments, rest = format_arguments [] args formals in
      let arguments = List.rev arguments in
      arguments, rest
    in
    {kf; callstack; arguments; rest; return; }

  let replace_value visitor substitution = function
    | Assign value -> Assign (Value.replace_base substitution value)
    | Copy (loc, flagged) ->
      let v = flagged.v >>-: Value.replace_base substitution in
      let flagged = { flagged with v } in
      let lloc = Location.replace_base substitution loc.lloc in
      let lval = Visitor.visitFramacLval visitor loc.lval in
      let loc = { loc with lval; lloc } in
      Copy (loc, flagged)

  let replace_recursive_call recursion call =
    let tbl = VarHashtbl.create 9 in
    List.iter (fun (v1, v2) -> VarHashtbl.add tbl v1 v2) recursion.substitution;
    let visitor = substitution_visitor tbl in
    let base_substitution = recursion.base_substitution in
    let replace_arg argument =
      let concrete = Visitor.visitFramacExpr visitor argument.concrete in
      let avalue = replace_value visitor base_substitution argument.avalue in
      { argument with concrete; avalue }
    in
    let arguments = List.map replace_arg call.arguments in
    { call with arguments; }

  let make_call ~subdivnb kf arguments valuation state =
    (* Evaluate the arguments of the call. *)
    let determinate = is_determinate kf in
    compute_actuals ~subdivnb ~determinate valuation state arguments
    >>=: fun (args, valuation) ->
    let call = create_call kf args in
    let recursion = Recursion.make call in
    let call = Extlib.opt_fold replace_recursive_call recursion call in
    call, recursion, valuation

  (* ----------------- show_each and dump_each directives ------------------- *)

  (* The product of domains formats the printing of each leaf domains, by
     checking their log_category and adding their name before the dump. If the
     domain is not a product, this needs to be done here. *)
  let print_state =
    if Domain.log_category = Domain_product.product_category
    then Domain.pretty
    else if Self.is_debug_key_enabled Domain.log_category
    then
      fun fmt state ->
        Format.fprintf fmt "# %s:@ @[<hv>%a@]@ " Domain.name Domain.pretty state
    else fun _ _ -> ()

  (* Frama_C_dump_each functions. *)
  let dump_state name state =
    Self.result ~current:true
      "%s:@\n@[<v>%a@]==END OF DUMP==%t"
      name print_state state Eva_utils.pp_callstack

  (* Idem as for [print_state]. *)
  let show_expr =
    if Domain.log_category = Domain_product.product_category
    then Domain.show_expr
    else if Self.is_debug_key_enabled Domain.log_category
    then
      fun valuation state fmt exp ->
        Format.fprintf fmt "# %s: @[<hov>%a@]"
          Domain.name (Domain.show_expr valuation state) exp
    else fun _ _ _ _ -> ()

  (* Frama_C_domain_show_each functions. *)
  let domain_show_each ~subdivnb name arguments state =
    let pretty fmt expr =
      let pp fmt  =
        match fst (Eval.evaluate ~subdivnb state expr) with
        | `Bottom ->
          Format.fprintf fmt "%s" (Unicode.bottom_string ())
        | `Value (valuation, _v) ->
          show_expr (Eval.to_domain_valuation valuation) state fmt expr
      in
      Format.fprintf fmt "%a : @[<h>%t@]" Printer.pp_exp expr pp
    in
    let pp = Pretty_utils.pp_list ~pre:"@[<v>" ~sep:"@ " ~suf:"@]" pretty in
    Self.result ~current:true
      "@[<v>%s:@ %a@]%t"
      name pp arguments Eva_utils.pp_callstack

  (* For non scalar expressions, prints the offsetmap of the cvalue domain. *)
  let show_offsm =
    match Domain.get_cvalue, Location.get Main_locations.PLoc.key with
    | None, _ | _, None ->
      fun fmt _ _ _ -> Format.fprintf fmt "%s" (Unicode.top_string ())
    | Some get_cvalue, Some get_ploc ->
      fun fmt subdivnb lval state ->
        try
          let offsm =
            let* (_, loc, _) =
              fst (Eval.lvaluate ~for_writing:false ~subdivnb state lval) in
            Eval_op.offsetmap_of_loc (get_ploc loc) (get_cvalue state)
          in
          let typ = Cil.typeOfLval lval in
          (Bottom.pretty (Eval_op.pretty_offsetmap typ)) fmt offsm
        with Abstract_interp.Error_Top ->
          Format.fprintf fmt "%s" (Unicode.top_string ())

  (* For scalar expressions, prints the cvalue component of their values. *)
  let show_value =
    match Value.get Main_values.CVal.key with
    | None -> fun fmt _ _ _ -> Format.fprintf fmt "%s" (Unicode.top_string ())
    | Some get_cval ->
      fun fmt subdivnb expr state ->
        let value =
          fst (Eval.evaluate ~subdivnb state expr) >>-: snd >>-: get_cval
        in
        (Bottom.pretty Cvalue.V.pretty) fmt value

  let pretty_arguments ~subdivnb state arguments =
    let is_scalar lval = Cil.isArithmeticOrPointerType (Cil.typeOfLval lval) in
    let pretty fmt expr =
      match expr.enode with
      | Lval lval | StartOf lval when not (is_scalar lval) ->
        show_offsm fmt subdivnb lval state
      | _ -> show_value fmt subdivnb expr state
    in
    Pretty_utils.pp_list ~pre:"@[<hv>" ~sep:",@ " ~suf:"@]" pretty arguments

  (* Frama_C_show_each functions. *)
  let show_each ~subdivnb name arguments state =
    Self.result ~current:true
      "@[<hv>%s:@ %a@]%t"
      name (pretty_arguments ~subdivnb state) arguments Eva_utils.pp_callstack

  (* Frama_C_dump_each_file functions. *)
  let dump_state_file_exc ~subdivnb name arguments state =
    let size = String.length name in
    let name =
      if size > 23
      (*  Frama_C_dump_each_file_ + 'something' *)
      then String.sub name 23 (size - 23)
      else failwith "no filename specified"
    in
    let n = try DumpFileCounters.find name with Not_found -> 0 in
    DumpFileCounters.add name (n+1);
    let file = Format.sprintf "%s_%d" name n in
    let ch = open_out file in
    let fmt = Format.formatter_of_out_channel ch in
    let l = fst (Cil.CurrentLoc.get ()) in
    Self.feedback ~current:true "Dumping state in file '%s'%t"
      file Eva_utils.pp_callstack;
    Format.fprintf fmt "DUMPING STATE at file %a line %d@."
      Datatype.Filepath.pretty l.Filepath.pos_path
      l.Filepath.pos_lnum;
    let pretty_args = pretty_arguments ~subdivnb state in
    if arguments <> []
    then Format.fprintf fmt "Args: %a@." pretty_args arguments;
    Format.fprintf fmt "@[<v>%a@]@?" print_state state;
    close_out ch

  let dump_state_file ~subdivnb name arguments state =
    try dump_state_file_exc ~subdivnb name arguments state
    with e ->
      Self.warning ~current:true ~once:true
        "Error during, or invalid call to Frama_C_dump_each_file (%s). Ignoring"
        (Printexc.to_string e)

  (** Applies the show_each or dump_each directives. *)
  let apply_special_directives ~subdivnb kf arguments state =
    let name = Kernel_function.get_name kf in
    if Ast_info.can_be_cea_function name
    then
      if Ast_info.is_cea_function name
      then (show_each ~subdivnb name arguments state; true)
      else if Ast_info.is_cea_domain_function name
      then (domain_show_each ~subdivnb name arguments state; true)
      else if Ast_info.is_cea_dump_file_function name
      then (dump_state_file ~subdivnb name arguments state; true)
      else if Ast_info.is_cea_dump_function name
      then (dump_state name state; true)
      else false
    else false

  (* Legacy callbacks for the cvalue domain, usually called by
     {Cvalue_transfer.start_call}. *)
  let apply_cvalue_callback kf ki_call state =
    let stack_with_call = (kf, ki_call) :: Eva_utils.call_stack () in
    let cvalue_state = Domain.get_cvalue_or_top state in
    Db.Value.Call_Value_Callbacks.apply (cvalue_state, stack_with_call);
    Db.Value.merge_initial_state (Eva_utils.call_stack ()) cvalue_state;
    Db.Value.Call_Type_Value_Callbacks.apply
      (`Builtin None, cvalue_state, stack_with_call)


  (* --------------------- Process the call statement ---------------------- *)

  let call stmt lval_option funcexp args state =
    let ki_call = Kstmt stmt in
    let subdivnb = subdivide_stmt stmt in
    (* Resolve [funcexp] into the called kernel functions. *)
    let functions, alarms =
      Eval.eval_function_exp ~subdivnb funcexp ~args state
    in
    Alarmset.emit ki_call alarms;
    let cacheable = ref Cacheable in
    let eval =
      let+ functions = functions in
      let process_one_function kf valuation =
        (* The special Frama_C_ functions to print states are handled here. *)
        if apply_special_directives ~subdivnb kf args state
        then
          let () = apply_cvalue_callback kf ki_call state in
          [(Partition.Key.empty, state)]
        else
          (* Create the call. *)
          let eval, alarms = make_call ~subdivnb kf args valuation state in
          Alarmset.emit ki_call alarms;
          let states =
            let+ call, recursion, valuation = eval in
            (* Do the call. *)
            let c, states =
              do_one_call valuation stmt lval_option call recursion state
            in
            (* If needed, propagate that callers cannot be cached. *)
            if c = NoCacheCallers then
              cacheable := NoCacheCallers;
            states
          in
          Bottom.list_of_bot states
      in
      (* Process each possible function apart, and append the result list. *)
      let process acc (kf, valuation) =
        process_one_function kf valuation @ acc
      in
      List.fold_left process [] functions
    in
    Bottom.list_of_bot eval, !cacheable

  (* ------------------------------------------------------------------------ *)
  (*                            Unspecified Sequence                          *)
  (* ------------------------------------------------------------------------ *)

  exception EBottom of Alarmset.t

  let process_truth ~alarm =
    let build_alarm status = Alarmset.singleton ~status (alarm ()) in
    function
    | `Unreachable           -> raise (EBottom Alarmset.none)
    | `False                 -> raise (EBottom (build_alarm Alarmset.False))
    | `Unknown _             -> build_alarm Alarmset.Unknown
    | `True | `TrueReduced _ -> Alarmset.none

  let check_non_overlapping state lvs1 lvs2 =
    let lvaluate ~valuation lval =
      fst (Eval.lvaluate ~valuation ~for_writing:false ~subdivnb:0 state lval)
    in
    let eval_loc (acc, valuation) lval =
      match lvaluate ~valuation lval with
      | `Bottom -> acc, valuation
      | `Value (valuation, loc, _) -> (lval, loc) :: acc, valuation
    in
    let eval_list valuation lvs =
      List.fold_left eval_loc ([], valuation) lvs
    in
    let list1, valuation = eval_list Eval.Valuation.empty lvs1 in
    let list2, _ = eval_list valuation lvs2 in
    let check acc (lval1, loc1) (lval2, loc2) =
      let truth = Location.assume_no_overlap ~partial:false loc1 loc2 in
      let alarm () = Alarms.Not_separated (lval1, lval2) in
      let alarm = process_truth ~alarm truth in
      Alarmset.combine alarm acc
    in
    Extlib.product_fold check Alarmset.none list1 list2

  (* Not currently taking advantage of calls information. But see
     plugin Undefined Order by VP. *)
  let check_unspecified_sequence stmt state seq =
    let check_stmt_pair acc statement1 statement2 =
      let stmt1, _, writes1, _, _ = statement1 in
      let stmt2, modified2, writes2, reads2, _ = statement2 in
      if stmt1 == stmt2 then acc else
        (* Values that cannot be read, as they are modified in the statement
           (but not by the whole sequence itself) *)
        let unauthorized_reads =
          List.filter
            (fun x -> List.for_all
                (fun y -> not (LvalStructEq.equal x y)) modified2)
            writes1
        in
        let alarms1 = check_non_overlapping state unauthorized_reads reads2 in
        let alarms =
          if stmt1.sid >= stmt2.sid then alarms1 else
            let alarms2 = check_non_overlapping state writes1 writes2 in
            Alarmset.combine alarms1 alarms2
        in
        Alarmset.combine alarms acc
    in
    try
      let alarms = Extlib.product_fold check_stmt_pair Alarmset.none seq seq in
      Alarmset.emit (Kstmt stmt) alarms;
      `Value ()
    with EBottom alarms -> Alarmset.emit (Kstmt stmt) alarms; `Bottom

  (* ------------------------------------------------------------------------ *)
  (*                               Enter Scope                                *)
  (* ------------------------------------------------------------------------ *)

  (* Makes the local variables [variables] enter the scope in [state].
     Also initializes volatile variable to top. *)
  let enter_scope kf variables state =
    let kind = Abstract_domain.Local kf in
    let state = Domain.enter_scope kind variables state in
    let is_volatile varinfo =
      Cil.typeHasQualifier "volatile" varinfo.vtype
    in
    let vars = List.filter is_volatile variables in
    let initialized = false in
    let init_value = Abstract_domain.Top in
    let initialize_volatile state varinfo =
      let lval = Cil.var varinfo in
      let location = Location.eval_varinfo varinfo in
      Domain.initialize_variable lval location ~initialized init_value state
    in
    List.fold_left initialize_volatile state vars
end


(*
Local Variables:
compile-command: "make -C ../../../.."
End:
*)
