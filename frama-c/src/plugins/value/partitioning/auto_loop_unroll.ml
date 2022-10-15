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

(* Heuristic for automatic loop unrolling: when the number of iterations of a
   loop can be bounded under a given limit, then unroll the loop.
   The limit is defined by the option -eva-auto-loop-unroll. *)

(* Gist of the heuristic:
   - collect loop exit conditions [cond] such as "if (cond) break;"
   - find a loop exit condition in which only one lvalue [lval] is modified
     within the loop; all other lvalues must be constant in the loop.
   - find a value [v_exit] such that [lval] ∈ [v_exit] ⇒ [cond] holds.
   - evaluate [lval] to its initial value [v_init] in the loop entry state.
   - compute an over-approximation of the increment [v_delta] of [lval] in one
     iteration of the loop.

   If [v_init] + k × [v_delta] ⊂ [v_exit], then the number of iterations
   is bounded by [k].

   The heuristic is syntactic and limited to the current function: it does not
   handle assignment through pointers or function calls.
   Thus, the condition [cond] should only contains direct accesses to variables
   whose address is never taken (they cannot be modified through pointers).
   If the loop contains a function call, the condition [cond] should not contain
   global variables (as they may be modified in the function called).
   If the loop contains no pointer writes and no function calls, the condition
   can also contains pointers to variables that are not modified within the loop.

   A first analysis of the loop gathers all variables modified within the
   loop; all others are constant, and can be evaluated in the loop entry state.

   When computing the increment [v_delta] of a lvalue [v] in the loop, the
   heuristic searches assignments "v = v ± i;". Otherwise, if [v] is only
   modified within the loop through an assignement "v = v2", the heuristic
   computes the initial value and delta increment of variable [v2] instead.
   This is required to deal with temporary variables introduced by the Frama-C
   normalization.
   Any other assignment of [v] cancels the heuristic. *)

open Cil_types

let is_true = function
  | `True | `TrueReduced _ -> true
  | _ -> false

(* Module for auxiliary functions manipulating interpreted automata. *)
module Graph = struct
  open Interpreted_automata

  type loop =
    { graph: G.t;   (* The complete graph of the englobing function. *)
      head: vertex; (* The head of the loop. *)
      wto: wto;     (* The wto for the loop body (without the loop head). *)
    }

  (* Builds the loop type for the englobing loop of statement [stmt]
     in function [kf]. Raises [Not_found] if no loop is found. *)
  let find_loop kf stmt =
    let automaton = get_automaton kf in
    let graph = automaton.graph in
    let vertex, _ = Cil_datatype.Stmt.Hashtbl.find automaton.stmt_table stmt in
    match get_wto_index kf vertex with
    | [] -> raise Not_found
    | head :: _ ->
      (* Find in the wto the component whose head is [head]. *)
      let rec find = function
        | [] -> assert false
        | Wto.Node _ :: tl -> find tl
        | Wto.Component (h, l) :: tl ->
          if Vertex.equal h head then {graph; head; wto = l} else find (l @ tl)
      in
      find (get_wto kf)

  (* Applies [f acc instr] to all instructions [instr] in the [loop]. *)
  let fold_instr f loop acc =
    let transfer (_v1, edge, _v2) acc =
      match edge.edge_transition with
      | Instr (instr, _stmt) -> f acc instr
      | _ -> acc
    in
    let compute_vertex = G.fold_pred_e transfer loop.graph in
    let wto = Wto.flatten loop.wto in
    List.fold_left (fun acc vertex -> compute_vertex vertex acc) acc wto

  (* Results for the simple dataflow analysis performed by [compute] below. *)
  module Results = Vertex.Hashtbl

  (* Simple dataflow analysis on [loop], with no fixpoint on inner nested loops.
     Starts with the value [init_value] at the head of the loop [loop.head],
     applies [transfer] to compute values through transitions in the loop body,
     and use [join] to merge values coming from different paths.
     If [backward] is set to [true], transitions are browsed in backward order.
     [transfer] has an argument [~inner_loop], which is true in inner loops.
     Returns the value computed for the loop head after one iteration of the
     loop. Paths outside the loop body are ignored. *)
  let compute ?(backward=false) loop transfer join init_value =
    let results = Results.create (G.nb_vertex loop.graph) in
    Results.add results loop.head init_value;
    let transfer_edge ~inner_loop (v1, edge, v2) acc =
      let v = if backward then v2 else v1 in
      match Results.find_opt results v with
      | None -> acc
      | Some value ->
        let value = transfer ~inner_loop value edge.edge_transition in
        match acc with
        | None -> Some value
        | Some acc -> Some (join acc value)
    in
    let compute_vertex =
      let fold = if backward then G.fold_succ_e else G.fold_pred_e in
      fun ~inner_loop vertex ->
        fold (transfer_edge ~inner_loop) loop.graph vertex None
    in
    let process_vertex ~inner_loop vertex =
      Option.iter (Results.add results vertex) (compute_vertex ~inner_loop vertex)
    in
    let sort = if backward then List.rev else fun x -> x in
    let rec iterate ~inner_loop = function
      | Wto.Node v -> process_vertex ~inner_loop v
      | Wto.Component (v, w) ->
        List.iter (iterate ~inner_loop:true) (sort (Wto.Node v :: w));
    in
    List.iter (iterate ~inner_loop:false) (sort loop.wto);
    compute_vertex ~inner_loop:false loop.head

  (* A loop exit condition is an expression and a boolean expression whether the
     expression must be zero or not-zero to exit the loop. *)
  module Condition = struct
    module Exp = Cil_datatype.ExpStructEq
    module Info = struct let module_name = "Condition" end
    include Datatype.Pair_with_collections (Exp) (Datatype.Bool) (Info)
  end

  (* Returns a list of loop exit conditions. *)
  let find_loop_exit_condition loop =
    let transfer ~inner_loop:_ conds = function
      | Guard (cond, kind, _) -> Condition.Set.add (cond, kind <> Then) conds
      | _ -> conds
    in
    let set = compute loop transfer Condition.Set.inter Condition.Set.empty in
    Option.fold ~none:[] ~some:Condition.Set.elements set
end

(* Effects of a loop:
   - set of varinfos that are directly modified within the loop. Pointer
     accesses are ignored.
   - does the loop contain a pointer write, a call or assemly code? *)
type loop_effect =
  { written_vars: Cil_datatype.Varinfo.Set.t;
    pointer_writes: bool;
    call: bool;
    assembly: bool; }

(* Adds a written variable to a loop_effect. *)
let add_written_var vi effect =
  let written_vars = Cil_datatype.Varinfo.Set.add vi effect.written_vars in
  { effect with written_vars }

let is_frama_c_builtin exp =
  match exp.enode with
  | Lval (Var vi, NoOffset) -> Ast_info.is_frama_c_builtin vi.vname
  | _ -> false

let compute_instr_effect effect = function
  | Set ((Var varinfo, _), _, _) -> add_written_var varinfo effect
  | Set ((Mem _, _), _, _) -> { effect with pointer_writes = true }
  | Call (Some (Var varinfo, _), _, _, _) ->
    { (add_written_var varinfo effect) with call = true; }
  | Call (Some (Mem _, _), _, _, _) ->
    { effect with pointer_writes = true; call = true; }
  | Call (None, exp, _, _) when not (is_frama_c_builtin exp) ->
    { effect with call = true }
  | Asm _ ->
    { effect with assembly = true }
  | _ -> effect

(* Computes the [loop_effect] of a [loop], by scanning all instructions of the
   loop body. *)
let compute_loop_effect loop =
  let acc =
    { written_vars = Cil_datatype.Varinfo.Set.empty;
      pointer_writes = false;
      call = false;
      assembly = false; }
  in
  let effect = Graph.fold_instr compute_instr_effect loop acc in
  if effect.assembly then None else Some effect

(* The status of a lvalue for the automatic loop unroll heuristic. *)
type var_status =
  | Constant  (* The lvalue is probably constant within the loop. *)
  | Candidate (* The lvalue is a good candidate for the heuristic:
                 integer type, access to a varinfo whose address is not taken,
                 modified within the loop but not in another function called
                 in the loop. *)
  | Unsuitable (* Cannot be used for the heuristic. *)

let is_integer lval = Cil.isIntegralType (Cil.typeOfLval lval)

(* Computes the status of a lvalue for the heuristic, according to the
   loop effects. Uses [eval_ptr] to compute the bases pointed by pointer
   expressions. *)
let classify eval_ptr loop_effect lval =
  let is_written varinfo =
    Cil_datatype.Varinfo.Set.mem varinfo loop_effect.written_vars
  in
  let rec is_const_expr expr =
    match expr.enode with
    | Lval lval -> classify_lval lval = Constant
    | UnOp (_, e, _) | CastE (_, e) -> is_const_expr e
    | BinOp (_, e1, e2, _) -> is_const_expr e1 && is_const_expr e2
    | Const _ | SizeOf _ | SizeOfE _ | SizeOfStr _
    | AlignOf _ | AlignOfE _ | AddrOf _ | StartOf _ -> true
  and classify_lval = function
    | Var varinfo, offset ->
      if (varinfo.vglob && loop_effect.call)
      || not (is_const_offset offset)
      then Unsuitable
      else if is_written varinfo
      then
        if is_integer lval && not varinfo.vaddrof then Candidate else Unsuitable
      else
        (* If the address of the variable is taken, it could be modified within
           the loop. We suppose here that this is not the case, but this could
           lead to some untimely loop unrolling. *)
        Constant
    | Mem expr, offset ->
      if not (loop_effect.pointer_writes || loop_effect.call)
      && is_const_expr expr && is_const_offset offset
      then
        match eval_ptr expr with
        | Some pointed when not (List.exists is_written pointed) -> Constant
        | _ -> Unsuitable
      else Unsuitable
  and is_const_offset = function
    | NoOffset -> true
    | Field (_, offset) -> is_const_offset offset
    | Index (e, offset) -> is_const_expr e && is_const_offset offset
  in
  classify_lval lval

(* Returns the list of all lvalues appearing in an expression. *)
let rec get_lvalues expr =
  match expr.enode with
  | Lval lval -> [ lval ]
  | UnOp (_, e, _) | CastE (_, e) -> get_lvalues e
  | BinOp (_op, e1, e2, _typ) -> get_lvalues e1 @ get_lvalues e2
  | Const _ | SizeOf _ | SizeOfE _ | SizeOfStr _
  | AlignOf _ | AlignOfE _ | AddrOf _ | StartOf _ -> []

(* Finds the unique candidate lvalue for the automatic loop unrolling
   heuristic in the expression [expr], if it exists. Returns None otherwise.  *)
let find_lonely_candidate eval_ptr loop_effect expr =
  let lvalues = get_lvalues expr in
  let rec aux acc list =
    match list with
    | [] -> acc
    | lval :: tl ->
      match classify eval_ptr loop_effect lval with
      | Unsuitable -> None
      | Constant   -> aux acc tl
      | Candidate  -> if acc = None then aux (Some lval) tl else None
  in
  aux None lvalues

(* Builds a transfer function suitable for [Graph.compute] that does nothing,
   except on assignemnts of [lval]:
   - to the value of an expression [expr], it applies [f expr acc];
   - to a function call, or if [inner_loop] is true, it raises [exn]. *)
let transfer_assign lval exn f ~inner_loop acc instr =
  let is_lval = Cil_datatype.LvalStructEq.equal lval in
  let transfer_instr ~inner_loop acc = function
    | Set (lv, expr, _loc) when is_lval lv ->
      if inner_loop then raise exn else f expr acc
    | Local_init (vi, AssignInit (SingleInit expr), _loc)
      when is_lval (Cil.var vi) && not inner_loop ->
      f expr acc
    | Local_init (vi, _, _) when is_lval (Cil.var vi) -> raise exn
    | Call (Some lv, _, _, _) when is_lval lv -> raise exn
    | _ -> acc
  in
  match instr with
  | Interpreted_automata.Instr (instr, _stmt) ->
    transfer_instr ~inner_loop acc instr
  | _ -> acc

(* If in the [loop], [lval] is always assigned to the value of another
   lvalue, returns this new lvalue. Otherwise, returns [lval]. *)
let cross_equality loop lval =
  (* If no such single equality can be found, return [lval] unchanged. *)
  let exception No_equality in
  let find_lval expr _x =
    match expr.enode with
    | Lval lval -> lval
    | _ -> raise No_equality
  in
  let transfer ~inner_loop lval instr =
    transfer_assign lval No_equality find_lval ~inner_loop lval instr
  in
  let join lv1 lv2 =
    if Cil_datatype.LvalStructEq.equal lv1 lv2 then lv1 else raise No_equality
  in
  match Graph.compute ~backward:true loop transfer join lval with
  | Some lval -> lval
  | None | exception No_equality -> lval

module Make (Abstract: Abstractions.Eva) = struct

  open Eval
  open Abstract
  module Valuation = Abstract.Eval.Valuation
  module Clear_Valuation = Clear_Valuation (Valuation)

  let (>>) v f = match v with `Value v -> f v | _ -> None
  let (>>=) v f = match v with Some v -> f v | None -> None

  (* Over-approximation of the change of an lvalue in one iteration of a loop,
     as a disjunction of:
     - the values directly assigned to the lvalue within the loop;
     - the increment/decrement of the lvalue in one iteration. *)
  type increment =
    { value: Val.t or_bottom; (* Possible values at the end of an iteration. *)
      delta: Val.t or_bottom; (* Possible increments in one iteration. *)
    }

  (* Raised when no increment can be computed for the given lvalue in one
     loop iteration. *)
  exception NoIncrement

  (* Adds or subtracts the integer value of [expr] to the current increment
     [acc.delta], according to [binop] which can be PlusA or MinusA.
     Raises NoIncrement if [expr] is not a constant integer expression. *)
  let add_to_delta binop acc expr =
    let typ = Cil.typeOf expr in
    match Cil.constFoldToInt expr with
    | None -> raise NoIncrement
    | Some i ->
      let add_to v =
        v >>- fun v -> Val.forward_binop typ binop v (Val.inject_int typ i)
      in
      { value = add_to acc.value; delta = add_to acc.delta; }

  (* Adds to [acc] the increment from the assignement of [lval] to the value
     of [expr]. Raises NoIncrement if this is not an increment of [lval]. *)
  let rec delta_assign lval expr acc =
    (* Is the expression [e] equal to the lvalue [lval] (modulo cast)? *)
    let rec is_lval e = match e.enode with
      | Lval lv -> Cil_datatype.LvalStructEq.equal lval lv
      | CastE (typ, e) -> Cil.isIntegralType typ && is_lval e
      | _ -> false
    in
    match Cil.constFoldToInt expr with
    | Some i ->
      let v = Val.inject_int (Cil.typeOf expr) i in
      { value = `Value v; delta = `Bottom; }
    | None ->
      match expr.enode with
      | BinOp ((PlusA | MinusA) as binop, e1, e2, _) ->
        if is_lval e1
        then add_to_delta binop acc e2
        else if is_lval e2 && binop = PlusA
        then add_to_delta binop acc e1
        else raise NoIncrement
      | CastE (typ, e) when Cil.isIntegralType typ -> delta_assign lval e acc
      | _ -> raise NoIncrement

  (* Computes an over-approximation of the increment of [lval] in the [loop].
     Only syntactic assignments of [lval] are considered, so [lval]
     should be a direct access to a variable whose address is not taken,
     and which should not be global if the loop contains function calls.
     Returns None if no increment can be computed. *)
  let compute_delta lval loop =
    let transfer = transfer_assign lval NoIncrement (delta_assign lval) in
    let join t1 t2 =
      { value = Bottom.join Val.join t1.value t2.value;
        delta = Bottom.join Val.join t1.delta t2.delta; }
    in
    let init = { value = `Bottom; delta = `Value Val.zero } in
    try Graph.compute loop transfer join init
    with NoIncrement -> None

  let cvalue_complement typ cvalue =
    let open Eval_typ in
    match Eval_typ.classify_as_scalar typ with
    | Some (TSFloat _ | TSPtr _) | None -> None
    | Some (TSInt ik) ->
      try
        let ival = Cvalue.V.project_ival cvalue in
        Ival.complement_int_under ~size:ik.i_bits ~signed:ik.i_signed ival
        >> fun ival -> Some (Cvalue.V.inject_ival ival)
      with Cvalue.V.Not_based_on_null -> None

  (* Reduces the condition "[condition] = [positive]" to a sufficient hypothesis
     on the value of the expression [expr]: computes a value [v] such that
     if the expression [expr] evaluates to [v], then [condition] = [positive].
     [valuation] contains additional hypotheses, i.e. the value of some constant
     lvalues of the [condition]. All computations must be done in the top state
     and in the given valuation. *)
  let reduce_to_expr valuation ~expr ~condition ~positive =
    let state = Abstract.Dom.top in
    (* Reduces [expr] by assuming that [condition] is [positive]. *)
    let reduce positive =
      (* Assumes that [condition] is [positive]. *)
      fst (Eval.reduce ~valuation state condition positive) >> fun valuation ->
      (* Finds the value of [expr] in the resulting valuation. *)
      Valuation.find valuation expr >> fun record ->
      record.value.v >> fun value ->
      (* If the new value of [expr] is top, no reduction has been performed. *)
      if Val.(equal top value) then None else Some (value, record)
    in
    (* Assumes that [condition] is [positive]. Returns an over-approximation
       of the values for which [condition] is [positive]. *)
    reduce positive >>= fun (value, record) ->
    (* Evaluates [condition] with the hypothesis [expr] ∈ [value], to check
       whether [expr] ∈ [value] ⇒ [condition] = [positive]. *)
    let valuation = Valuation.add valuation expr record in
    fst (Eval.evaluate ~valuation ~reduction:false state condition)
    >> fun (_valuation, v) ->
    let satisfied =
      if positive
      then not Val.(is_included zero v)
      else Val.(equal zero v)
    in
    (* If the condition is satisfied, returns [value]. Otherwise, uses a
       specific feature to cvalue (if possible) to compute a better value. *)
    if satisfied then Some value else
      Val.get Main_values.CVal.key >>= fun get_cvalue ->
      (* Assumes that [condition] is NOT [positive]. *)
      reduce (not positive) >>= fun (value, _record) ->
      (* [value] is an over-approximation of the values of [expr] for which
         [condition] is NOT positive; its complement is an under-approximation
         of the values for which [condition] is positive. *)
      let cvalue = get_cvalue value in
      cvalue_complement (Cil.typeOf expr) cvalue >>= fun cvalue ->
      Some (Val.set Main_values.CVal.key cvalue Val.top)

  (* If [lval] is a varinfo out-of-scope at statement [stmt] of function [kf],
     introduces it to the [state]. *)
  let enter_scope state kf stmt = function
    | Var vi, _ ->
      let state =
        if vi.vglob || vi.vformal || Kernel_function.var_is_in_scope stmt vi
        then state
        else Abstract.Dom.enter_scope (Abstract_domain.Local kf) [vi] state
      in
      let location = Abstract.Loc.eval_varinfo vi in
      Abstract.Dom.logic_assign None location state
    | _ -> state

  (* Same as [reduce_to_expr] above, but builds the proper valuation from the
     [state]. [state] is the entry state of the loop, and [lval] is the only
     part of [condition] that is not constant within the loop. [state] can thus
     be used to evaluate all other subparts of [condition], before computing
     the value of [lval] that satisfies [condition]. *)
  let reduce_to_lval state kf stmt lval condition positive =
    (* If [lval] is not in scope at [stmt], introduces it into [state] so that
       the [condition] can be properly evaluated in [state]. *)
    let state = enter_scope state kf stmt lval in
    let expr = Cil.new_exp ~loc:condition.eloc (Lval lval) in
    (* Evaluate the [condition] in the given [state]. *)
    fst (Eval.evaluate state condition) >> fun (valuation, _v) ->
    (* In the resulting valuation, replace the value of [expr] by [top_int]
       and removes all expressions depending on [expr]. *)
    Valuation.find valuation expr >> fun record ->
    let value = { record.value with v = `Value Val.top_int } in
    let record = { record with value } in
    let valuation =
      Clear_Valuation.clear_englobing_exprs
        valuation ~expr:condition ~subexpr:expr
    in
    let valuation = Valuation.add valuation expr record in
    reduce_to_expr valuation ~expr ~condition ~positive

  (* Evaluates the lvalue [lval] in the state [state]. Returns None if the value
     may be undeterminate. *)
  let evaluate_lvalue state lval =
    fst (Eval.copy_lvalue state lval) >> fun (_valuation, flagged_value) ->
    if not flagged_value.initialized || flagged_value.escaping
    then None
    else flagged_value.v >> fun v -> Some v

  (* Computes the bases pointed by a pointer expression [expr] in [state].  *)
  let evaluate_pointer state expr =
    Val.get Main_values.CVal.key >>= fun get_cvalue ->
    fst (Eval.evaluate state expr) >> fun (_valuation, v) ->
    let cvalue = get_cvalue v in
    match Cvalue.V.get_bases cvalue with
    | Base.SetLattice.Top -> None
    | Base.SetLattice.Set bases ->
      try
        let varinfo_list =
          Base.Hptset.fold (fun base acc -> Base.to_varinfo base :: acc) bases []
        in
        Some varinfo_list
      with Base.Not_a_C_variable -> None

  let (>>:) v f = match v with Some v -> f v | None -> false

  (* Is the number of iterations of a loop bounded by [limit]?
     [state] is the loop entry state, and [loop_block] the block of the loop. *)
  let is_bounded_loop kf stmt loop state limit =
    (* Computes the effect of the loop. Stops if it contains assembly code. *)
    compute_loop_effect loop >>: fun loop_effect ->
    (* Finds loop exit conditions. *)
    let exit_conditions = Graph.find_loop_exit_condition loop in
    (* Does the condition [condition = positive] limits the number of iterations
       of the loop by [limit]? *)
    let is_bounded_by_condition (condition, positive) =
      let eval_ptr = evaluate_pointer state in
      (* Finds the unique integer lvalue modified within the loop in [condition].
         Stops if it does not exist is not a good candidate for the heuristic. *)
      find_lonely_candidate eval_ptr loop_effect condition >>: fun lval ->
      (* Reduce [condition] to a sufficient hypothesis over the [lval] value:
         if [lval] ∈ [v_exit] then [condition = positive]. *)
      reduce_to_lval state kf stmt lval condition positive >>: fun v_exit ->
      (* If [lval] is only assigned to the value of another lvalue, uses it
         instead. This is especially useful to deal with temporary variables
         introduced by the Frama-C normalization. *)
      let lval = cross_equality loop lval in
      (* Evaluates the initial value [v_init] of [lval] in the loop entry state. *)
      evaluate_lvalue state lval >>: fun v_init ->
      (* Computes an over-approximation [v_incr] of the value update of [lval]
         in one iteration of the loop. *)
      compute_delta lval loop >>: fun v_incr ->
      let typ = Cil.typeOfLval lval in
      let binop op v1 v2 = Bottom.non_bottom (Val.forward_binop typ op v1 v2) in
      (* Computes the possible values of [lval] after n loop iterations. *)
      let value =
        (* [delta] is the possible increments of [lval] in one iteration. *)
        v_incr.delta >>-: fun delta ->
        (* If [delta] can be zero, then [lval] can be unchanged in an iteration,
           and the loop may never terminate: we abort the heuristic. *)
        if not (is_true (Val.assume_non_zero delta)) then raise Not_found;
        (* Possible iterations numbers to exit the loop. *)
        let iter_nb = binop Div (binop MinusA v_exit v_init) delta in
        let bound = Abstract_value.Int (Integer.of_int limit) in
        (* Use the iteration number if it is always smaller than the [limit].
           Otherwise use [limit]. *)
        let limit =
          if is_true (Val.assume_bounded Alarms.Upper_bound bound iter_nb)
          then iter_nb
          else Val.inject_int typ (Integer.of_int limit)
        in
        (* Computes the possible values of [lval] as the end of the loop, as
           [v_init] + [limit] × [v_delta]. *)
        binop PlusA v_init (binop Mult limit delta)
      in
      (* [v_incr.value] are possible values for [lval] at the end of an
         iteration, without increment/decrement. *)
      let final_value = Bottom.join Val.join value v_incr.value in
      (* Checks whether [final_value] ⊂ [v_exit], a sufficient condition
         to exit the loop. *)
      Bottom.is_included Val.is_included final_value (`Value v_exit)
    in
    (* Tests whether at least one of the exit conditions limits the number of
       iteration by [limit]. *)
    List.exists is_bounded_by_condition exit_conditions

  (* Computes an automatic loop unrolling for statement [stmt] in state [state],
     with a maximum limit. Returns None for no automatic loop unrolling. *)
  let compute ~max_unroll state stmt =
    try
      let kf = Kernel_function.find_englobing_kf stmt in
      let loop = Graph.find_loop kf stmt in
      if is_bounded_loop kf stmt loop state max_unroll
      then Some max_unroll
      else None
    with Not_found -> None
end
