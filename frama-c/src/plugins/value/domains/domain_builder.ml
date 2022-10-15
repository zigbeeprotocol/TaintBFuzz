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

module type InputDomain = sig
  include Datatype.S
  val top: t
  val join: t -> t -> t
end

module type LeafDomain = sig
  type t

  val backward_location: t -> lval -> typ -> 'loc -> 'v -> ('loc * 'v) or_bottom
  val reduce_further: t -> exp -> 'v -> (exp * 'v) list

  val evaluate_predicate:
    t Abstract_domain.logic_environment -> t -> predicate -> Alarmset.status
  val reduce_by_predicate:
    t Abstract_domain.logic_environment -> t -> predicate -> bool -> t or_bottom
  val interpret_acsl_extension:
    acsl_extension -> t Abstract_domain.logic_environment -> t -> t

  val enter_loop: stmt -> t -> t
  val incr_loop_counter: stmt -> t -> t
  val leave_loop: stmt -> t -> t

  val filter: kernel_function -> [`Pre | `Post] -> Base.Hptset.t -> t -> t
  val reuse:
    kernel_function -> Base.Hptset.t ->
    current_input:t -> previous_output:t -> t

  val show_expr: 'a -> t -> Format.formatter -> exp -> unit
  val post_analysis: t Lattice_bounds.or_bottom -> unit

  module Store: Domain_store.S with type t := t

  val key: t Abstract_domain.key
end

module Complete (Domain: InputDomain) = struct

  let backward_location _state _lval _typ loc value = `Value (loc, value)
  let reduce_further _state _expr _value = []

  let evaluate_predicate _env _state _predicate = Alarmset.Unknown
  let reduce_by_predicate _env state _predicate _positive = `Value state
  let interpret_acsl_extension _extension _env state = state

  let enter_loop _stmt state = state
  let incr_loop_counter _stmt state = state
  let leave_loop _stmt state = state

  let filter _kf _kind _bases state = state
  let reuse _kf _bases ~current_input:_ ~previous_output = previous_output

  let show_expr _valuation _state fmt _expr =
    Format.fprintf fmt "(not implemented)"

  let post_analysis _state = ()

  module Store = Domain_store.Make (Domain)

  let key: Domain.t Structure.Key_Domain.key =
    Structure.Key_Domain.create_key Domain.name
end

open Simpler_domains

let simplify_argument argument =
  { formal = argument.Eval.formal;
    concrete = argument.Eval.concrete }

let simplify_call call =
  { kf = call.Eval.kf;
    arguments = List.map simplify_argument call.Eval.arguments;
    rest = List.map fst call.Eval.rest;
    return = call.Eval.return; }

module Make_Minimal
    (Value: Abstract_value.S)
    (Location: Abstract_location.S)
    (Domain: Simpler_domains.Minimal)
= struct

  include Domain

  let log_category = Self.register_category ("d-" ^ name)

  type value = Value.t
  type location = Location.location
  type state = Domain.t
  type origin

  let narrow x _y = `Value x

  let top_answer = `Value (Value.top, None), Alarmset.all
  let extract_expr ~oracle:_ _context _state _expr = top_answer
  let extract_lval ~oracle:_ _context _state _lval _typ _location = top_answer

  let update _valuation state = `Value state

  let assign kinstr lv expr _value _valuation state =
    Domain.assign kinstr lv.Eval.lval expr state

  let assume stmt expr positive _valuation state =
    Domain.assume stmt expr positive state

  let start_call stmt call recursion _valuation state =
    match recursion with
    | None -> `Value (Domain.start_call stmt (simplify_call call) state)
    | Some _ ->
      (* TODO *)
      Self.abort
        "The domain %s does not support recursive call." Domain.name

  let finalize_call stmt call recursion ~pre ~post =
    assert (recursion = None);
    Domain.finalize_call stmt (simplify_call call) ~pre ~post

  let initialize_variable lval _location ~initialized value state =
    Domain.initialize_variable lval ~initialized value state

  let initialize_variable_using_type _kind varinfo state =
    let lval = Cil.var varinfo in
    Domain.initialize_variable lval ~initialized:true Abstract_domain.Top state

  let logic_assign _assigns _location _state = top

  let relate _kf _bases _state = Base.SetLattice.top
end


module Complete_Minimal
    (Value: Abstract_value.S)
    (Location: Abstract_location.S)
    (Domain: Simpler_domains.Minimal)
= struct

  module D = struct
    include Make_Minimal (Value) (Location) (Domain)

    include
      (Datatype.Make_with_collections
         (struct
           include Datatype.Undefined
           type t = Domain.t
           let name = Domain.name
           let reprs = [ Domain.top ]
           let equal x y = Domain.compare x y = 0
           let compare = Domain.compare
           let hash = Domain.hash
           let pretty = Domain.pretty
           let mem_project = Datatype.never_any_project
         end)
       : Datatype.S_with_collections with type t := t)
  end

  include D
  include Complete (D)

end


module Complete_Minimal_with_datatype
    (Value: Abstract_value.S)
    (Location: Abstract_location.S)
    (Domain: Minimal_with_datatype)
= struct

  module D = struct

    include Make_Minimal (Value) (Location) (Domain)

    include
      (Datatype.With_collections
         (Domain) (struct let module_name = Domain.name end)
       : Datatype.S_with_collections with type t := t)
  end

  include D
  include Complete (D)

end

open Eval

module Complete_Simple_Cvalue (Domain: Simpler_domains.Simple_Cvalue)
= struct

  module D = struct
    include Domain

    include
      (Datatype.With_collections
         (Domain) (struct let module_name = Domain.name end)
       : Datatype.S_with_collections with type t := t)

    let log_category = Self.register_category ("d-" ^ name)

    type value = Cvalue.V.t
    type location = Precise_locs.precise_location
    type state = Domain.t
    type origin

    let narrow x _y = `Value x

    let extract_expr ~oracle:_ _context state expr =
      let v = Domain.extract_expr state expr >>-: fun v -> v, None in
      v, Alarmset.all

    let extract_lval ~oracle:_ _context state lval typ location =
      let v = Domain.extract_lval state lval typ location >>-: fun v -> v, None in
      v, Alarmset.all

    let find valuation expr =
      match valuation.Abstract_domain.find expr with
      | `Top -> `Top
      | `Value record -> `Value record.value

    let find_loc valuation lval =
      match valuation.Abstract_domain.find_loc lval with
      | `Top -> `Top
      | `Value record -> `Value record.loc

    let record valuation = { find = find valuation;
                             find_loc = find_loc valuation; }

    let update _valuation state = `Value state
    let assign kinstr lv expr value valuation state =
      Domain.assign kinstr lv expr value (record valuation) state
    let assume stmt expr positive valuation state =
      Domain.assume stmt expr positive (record valuation) state

    let start_call stmt call recursion valuation state =
      match recursion with
      | None -> `Value (Domain.start_call stmt call (record valuation) state)
      | Some _ ->
        (* TODO *)
        Self.abort
          "The domain %s does not support recursive call." Domain.name

    let finalize_call stmt call recursion =
      assert (recursion = None);
      Domain.finalize_call stmt call

    let initialize_variable lval _location ~initialized value state =
      Domain.initialize_variable lval ~initialized value state

    let initialize_variable_using_type _kind varinfo state =
      let lval = Cil.var varinfo in
      Domain.initialize_variable lval ~initialized:true Abstract_domain.Top state

    let logic_assign _assigns _location _state = top

    let relate _kf _bases _state = Base.SetLattice.top
  end

  include D
  include Complete (D)
end

(* -------------------------------------------------------------------------- *)

module Restrict
    (Value: Abstract_value.S)
    (Domain: Abstract.Domain.Internal with type value = Value.t)
    (Scope: sig val functions: Domain_mode.function_mode list end)
= struct

  open Domain_mode

  (* Defines the join and the narrow of different modes. *)
  module Mode = struct
    include Mode

    let merge f m1 m2 =
      let merge_perm p1 p2 =
        { read = f p1.read p2.read;
          write = f p1.write p2.write; }
      in
      { current = merge_perm m1.current m2.current;
        calls = merge_perm m1.calls m2.calls; }

    let join = merge (&&)
    let narrow = merge (||)
  end

  (* Map that binds functions to their analysis mode. *)
  let functions_map =
    List.fold_left
      (fun map (kf, mode) -> Kernel_function.Map.add kf mode map)
      Kernel_function.Map.empty Scope.functions

  (* This module propagates states of type [(state * mode) option]:
     - None is propagated as long as no functions from [Scope.functions]
       are analyzed.
     - then the current [mode] is propagated alongside the state. Queries and
       transfer functions are applied accordingly. The current mode is replaced
       at function calls by [mode.calls]. *)

  module Info = struct let module_name = Domain.name ^ " restricted" end
  module D = Datatype.Pair_with_collections (Domain) (Mode) (Info)

  module I = struct let module_name = Domain.name ^ " option" end
  include Datatype.Option_with_collections (D) (I)

  let default = Domain.top, Mode.all
  let structure: t Abstract.Domain.structure =
    Abstract.Domain.(Option ((Node (Domain.structure, Void)), default))

  type state = t
  type value = Domain.value
  type location = Domain.location
  type origin = Domain.origin

  let get_state = function
    | None -> Domain.top
    | Some (state, _mode) -> state

  (* When the first function from [Scope.functions] is encountered, starts the
     analysis with the state computed by this function. It is an empty state in
     which the global variables exist and may have any values. *)
  let compute_starting_state () =
    let empty = Domain.empty () in
    let var_kind = Abstract_domain.Global in
    let init varinfo _init state =
      let state = Domain.enter_scope var_kind [varinfo] state in
      Domain.initialize_variable_using_type var_kind varinfo state
    in
    Globals.Vars.fold init empty

  (* Do not recompute each time the starting state. Do not compute the starting
     state too early either, in case it depends on analysis options. *)
  let get_starting_state =
    let starting_state = ref None in
    fun () ->
      match !starting_state with
      | None ->
        let s = compute_starting_state () in
        starting_state := Some s;
        s
      | Some state -> state

  (* ----- Lattice ---------------------------------------------------------- *)

  let top = None

  let is_included x y =
    match x, y with
    | _, None -> true
    | None, _ -> false
    | Some (d1, _), Some (d2, _) -> Domain.is_included d1 d2

  let make_join join = fun x y ->
    match x, y with
    | None, _ | _, None -> None
    | Some (d1, m1), Some (d2, m2) -> Some (join d1 d2, Mode.join m1 m2)

  let join = make_join Domain.join
  let widen kf stmt = make_join (Domain.widen kf stmt)

  let narrow x y =
    match x, y with
    | None, s | s, None -> `Value s
    | Some (d1, s1), Some (d2, s2) ->
      Domain.narrow d1 d2 >>-: fun s ->
      Some (s, Mode.narrow s1 s2)

  (* ----- Queries ---------------------------------------------------------- *)

  (* Applies the [query] only if the current mode allows the domain to read.
     Otherwise, returns [default]. *)
  let make_query default query = function
    | None -> default
    | Some (state, mode) ->
      if mode.current.read
      then query state
      else default

  let default_query = `Value (Value.top, None), Alarmset.all

  let extract_expr ~oracle context state expr =
    make_query default_query
      (fun s -> Domain.extract_expr ~oracle context s expr) state

  let extract_lval ~oracle context state lval typ location =
    make_query
      default_query
      (fun s -> Domain.extract_lval ~oracle context s lval typ location)
      state

  let backward_location state lval typ location value =
    make_query
      (`Value (location, value))
      (fun s -> Domain.backward_location s lval typ location value)
      state

  let reduce_further state expr value =
    make_query [] (fun s -> Domain.reduce_further s expr value) state

  (* ----- Transfer functions ----------------------------------------------- *)

  (* Applies the transfer function [f] only if the current mode allows the
     domain to write. Otherwise, returns the state unchanged. *)
  let make_transfer f = function
    | None -> `Value None
    | Some (state, mode) ->
      if mode.current.write
      then f state >>-: fun state -> Some (state, mode)
      else `Value (Some (state, mode))

  let update valuation = make_transfer (Domain.update valuation)
  let assume stmt expr positive valuation =
    make_transfer (Domain.assume stmt expr positive valuation)

  (* Applies the [assign] transfer function according to the current mode.
     In any case, removes from the state the properties depending on the memory
     location modified by the assignment. *)
  let assign kinstr lvalue expr assigned valuation = function
    | None -> `Value None
    | Some (state, mode) ->
      if mode.current.write
      then
        Domain.assign kinstr lvalue expr assigned valuation state >>-: fun s ->
        Some (s, mode)
      else
        let state = Domain.logic_assign None lvalue.lloc state in
        `Value (Some (state, mode))

  (* Starts an analysis at call [call] with state [state]. The domain was not
     enabled before this call: the concrete arguments may contain variables that
     have never been introduced into the state, so we should not use them. This
     function only introduces the formal parameters in the state. *)
  let start_analysis call state =
    let formals = List.map (fun argument -> argument.formal) call.arguments in
    let kind = Abstract_domain.Formal call.kf in
    let state = Domain.enter_scope kind formals state in
    let initialize acc v = Domain.initialize_variable_using_type kind v acc in
    let state = List.fold_left initialize state formals in
    state

  (* When interpreting a function call:
     - if the mode of the function called allows the domain to infer properties,
       use [start_call] and [finalize_call] as normal. If the current mode did
       not allow the domain to infer properties, use [start_analysis] instead.
     - otherwise, only propagate the state from the call site to kill the
       properties that depend on locations written in the called functions. *)

  let start_call stmt call recursion valuation state =
    (* Starts the call with mode [new_mode]. [previous_mode] is the current mode
       of the caller. *)
    let start_call_with_mode ?previous_mode ~new_mode state =
      if new_mode.current.write
      then
        match previous_mode with
        | Some mode when mode.current.write ->
          Domain.start_call stmt call recursion valuation state >>-: fun state ->
          Some (state, new_mode)
        | _ ->
          `Value (Some (start_analysis call state, new_mode))
      else `Value (Some (state, new_mode))
    in
    (* If an analysis mode is defined for the called function in [Scope],
       then this mode becomes the new current mode. Otherwise, use the [calls]
       field of the previous mode. *)
    let called_mode = Kernel_function.Map.find_opt call.kf functions_map in
    match state, called_mode with
    | Some (state, previous_mode), Some new_mode ->
      start_call_with_mode ~previous_mode ~new_mode state
    | Some (state, previous_mode), None ->
      let new_mode = { previous_mode with current = previous_mode.calls } in
      start_call_with_mode ~previous_mode ~new_mode state
    | None, Some new_mode ->
      start_call_with_mode ~new_mode (get_starting_state ())
    | None, None ->
      `Value None

  let finalize_call stmt call recursion ~pre ~post =
    match pre, post with
    | None, _ | _, None -> `Value None
    | Some (pre, pre_mode), Some (post, post_mode) ->
      if post_mode.current.write
      then
        Domain.finalize_call stmt call recursion ~pre ~post >>-: fun state ->
        Some (state, pre_mode)
      else
        `Value (Some (post, pre_mode))

  let show_expr valuation state fmt expr =
    match state with
    | None -> ()
    | Some (state, _mode) -> Domain.show_expr valuation state fmt expr

  (* ----- Logic evalutation ------------------------------------------------ *)

  let logic_assign assign location = function
    | None -> None
    | Some (state, mode) ->
      let assign =
        Option.map (fun (assign, state) -> assign, get_state state) assign
      in
      Some (Domain.logic_assign assign location state, mode)

  let lift_env env =
    let states label = get_state (env.Abstract_domain.states label) in
    Abstract_domain.{ env with states = states }

  let evaluate_predicate env state predicate =
    make_query
      Alarmset.Unknown
      (fun s -> Domain.evaluate_predicate (lift_env env) s predicate)
      state

  let reduce_by_predicate env state predicate positive =
    make_transfer
      (fun s -> Domain.reduce_by_predicate (lift_env env) s predicate positive)
      state

  (* ----- Scoping, initialization & loops ---------------------------------- *)

  let lift f = function
    | None -> None
    | Some (state, mode) as x ->
      if mode.current.write
      then Some (f state, mode)
      else x

  let interpret_acsl_extension extension env =
    lift (Domain.interpret_acsl_extension extension (lift_env env))

  let enter_scope kind varinfos = lift (Domain.enter_scope kind varinfos)
  let leave_scope kf varinfos = lift (Domain.leave_scope kf varinfos)

  (* Uses the mode of the 'main' function to start the analysis. *)
  let empty () =
    let main_kf = fst (Globals.entry_point ()) in
    match Kernel_function.Map.find_opt main_kf functions_map with
    | None -> None
    | Some mode -> Some (Domain.empty (), mode)

  let initialize_variable lval location ~initialized init_value =
    lift (Domain.initialize_variable lval location ~initialized init_value)
  let initialize_variable_using_type init_kind varinfo =
    lift (Domain.initialize_variable_using_type init_kind varinfo)

  let enter_loop stmt = lift (Domain.enter_loop stmt)
  let incr_loop_counter stmt = lift (Domain.incr_loop_counter stmt)
  let leave_loop stmt = lift (Domain.leave_loop stmt)

  (* ----- MemExec ---------------------------------------------------------- *)

  let relate kf bases = function
    | None -> Base.SetLattice.empty
    | Some (state, _mode) -> Domain.relate kf bases state

  let filter kf kind bases = function
    | None -> None
    | Some (state, mode) -> Some (Domain.filter kf kind bases state, mode)

  let reuse kf bases ~current_input ~previous_output =
    match current_input, previous_output with
    | None, _ | _, None -> None
    | Some (current_input, mode), Some (previous_output, _) ->
      Some (Domain.reuse kf bases ~current_input ~previous_output, mode)

  let log_category = Domain.log_category

  let post_analysis state =
    let state = state >>-: get_state in
    Domain.post_analysis state

  (* ----- Storage ---------------------------------------------------------- *)

  module Store = struct

    let register_global_state b state =
      let state = state >>-: get_state in
      Domain.Store.register_global_state b state

    let lift_register f state = f (get_state state)

    let register_initial_state callstack =
      lift_register (Domain.Store.register_initial_state callstack)
    let register_state_before_stmt callstack stmt =
      lift_register (Domain.Store.register_state_before_stmt callstack stmt)
    let register_state_after_stmt callstack stmt =
      lift_register (Domain.Store.register_state_after_stmt callstack stmt)

    let inject state = Some (state, Mode.all)

    let get_global_state () = Domain.Store.get_global_state () >>-: inject
    let get_initial_state kf = Domain.Store.get_initial_state kf >>-: inject
    let get_stmt_state ~after stmt =
      Domain.Store.get_stmt_state ~after stmt >>-: inject

    let inject_table = function
      | `Top -> `Top
      | `Bottom -> `Bottom
      | `Value t ->
        let module Hashtbl = Value_types.Callstack.Hashtbl in
        let table = Hashtbl.create (Hashtbl.length t) in
        Hashtbl.iter (fun key s -> Hashtbl.add table key (inject s)) t;
        `Value table

    let get_initial_state_by_callstack ?selection kf =
      inject_table (Domain.Store.get_initial_state_by_callstack ?selection kf)
    let get_stmt_state_by_callstack ?selection ~after stmt =
      inject_table
        (Domain.Store.get_stmt_state_by_callstack ?selection ~after stmt)

    let mark_as_computed = Domain.Store.mark_as_computed
    let is_computed = Domain.Store.is_computed
  end
end
