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

type computation_state = Self.computation_state =
  | NotComputed | Computing | Computed | Aborted
let current_computation_state = Self.current_computation_state
let register_computation_hook = Self.register_computation_hook
let is_computed = Self.is_computed
let self = Self.state

type results = Function_calls.results = Complete | Partial | NoResults
type status = Function_calls.analysis_status =
    Unreachable | SpecUsed | Builtin of string | Analyzed of results
let status kf =
  match Function_calls.analysis_status kf with
  | Analyzed Complete as status ->
    if is_computed () then status else Analyzed Partial
  | status -> status

let use_spec_instead_of_definition =
  Function_calls.use_spec_instead_of_definition ?recursion_depth:None

let save_results kf =
  try Function_calls.save_results (Kernel_function.get_definition kf)
  with Kernel_function.No_Definition -> false

module type Results = sig
  type state
  type value
  type location

  val get_global_state: unit -> state or_top_bottom
  val get_stmt_state : after:bool -> stmt -> state or_top_bottom
  val get_stmt_state_by_callstack:
    ?selection:callstack list ->
    after:bool -> stmt -> state Value_types.Callstack.Hashtbl.t or_top_bottom
  val get_initial_state:
    kernel_function -> state or_top_bottom
  val get_initial_state_by_callstack:
    ?selection:callstack list ->
    kernel_function -> state Value_types.Callstack.Hashtbl.t or_top_bottom

  val eval_expr : state -> exp -> value evaluated
  val copy_lvalue: state -> lval -> value flagged_value evaluated
  val eval_lval_to_loc: state -> lval -> location evaluated
  val eval_function_exp:
    state -> ?args:exp list -> exp ->  kernel_function list evaluated
  val assume_cond : stmt -> state -> exp -> bool -> state or_bottom
end

module type S = sig
  include Abstractions.Eva
  include Results with type state := Dom.state
                   and type value := Val.t
                   and type location := Loc.location
end

module type Analyzer = sig
  include S
  val compute_from_entry_point : kernel_function -> lib_entry:bool -> unit
  val compute_from_init_state: kernel_function -> Dom.t -> unit
  val initial_state: lib_entry:bool -> Dom.t or_bottom
end


module Make (Abstract: Abstractions.S) = struct

  module Abstract = struct
    include Abstract
    module Eval = Evaluation.Make (Abstract.Val) (Abstract.Loc) (Abstract.Dom)
  end

  include Abstract
  include Compute_functions.Make (Abstract)

  let find stmt f =
    if is_computed ()
    then
      let kf = Kernel_function.find_englobing_kf stmt in
      match status kf with
      | Unreachable | SpecUsed | Builtin _ -> `Bottom
      | Analyzed NoResults -> `Top
      | Analyzed (Complete | Partial) -> f stmt
    else `Top

  let get_stmt_state ~after stmt =
    find stmt (Dom.Store.get_stmt_state ~after :> stmt -> Dom.t or_top_bottom)

  let get_stmt_state_by_callstack ?selection ~after stmt =
    find stmt (Abstract.Dom.Store.get_stmt_state_by_callstack ?selection ~after)

  let get_global_state () =
    (Abstract.Dom.Store.get_global_state () :> Dom.t or_top_bottom)

  let get_initial_state kf =
    if is_computed () then
      if Function_calls.is_called kf
      then (Abstract.Dom.Store.get_initial_state kf :> Dom.t or_top_bottom)
      else `Bottom
    else `Top

  let get_initial_state_by_callstack ?selection kf =
    if is_computed () then
      if Function_calls.is_called kf
      then Abstract.Dom.Store.get_initial_state_by_callstack ?selection kf
      else `Bottom
    else `Top

  let eval_expr state expr = Eval.evaluate state expr >>=: snd

  let copy_lvalue state expr = Eval.copy_lvalue state expr >>=: snd

  let eval_lval_to_loc state lv =
    let get_loc (_, loc, _) = loc in
    let for_writing = false in
    Eval.lvaluate ~for_writing state lv >>=: get_loc

  let eval_function_exp state ?args e =
    Eval.eval_function_exp e ?args state >>=: (List.map fst)

  let assume_cond stmt state cond positive =
    fst (Eval.reduce state cond positive) >>- fun valuation ->
    let dval = Eval.to_domain_valuation valuation in
    Dom.assume stmt cond positive dval state

end


module Legacy = Make (Abstractions.Legacy)

module Default =
  (val
    (if Abstractions.Config.(equal default legacy)
     then (module Legacy)
     else (module Make (Abstractions.Default)))
    : Analyzer)

(* Reference to the current configuration (built by Abstractions.configure from
   the parameters of Eva regarding the abstractions used in the analysis) and
   the current Analyzer module. *)
let ref_analyzer =
  ref (Abstractions.Config.default, (module Default : Analyzer))

(* Returns the current Analyzer module. *)
let current_analyzer () = (module (val (snd !ref_analyzer)): S)

(* Set of hooks called whenever the current Analyzer module is changed.
   Useful for the GUI parts that depend on it. *)
module Analyzer_Hook = Hook.Build (struct type t = (module S) end)

(* Register a new hook. *)
let register_hook = Analyzer_Hook.extend

(* Sets the current Analyzer module for a given configuration.
   Calls the hooks above. *)
let set_current_analyzer config (analyzer: (module Analyzer)) =
  Analyzer_Hook.apply (module (val analyzer): S);
  ref_analyzer := (config, analyzer)

let cvalue_initial_state () =
  let module A = (val snd !ref_analyzer) in
  let _, lib_entry = Globals.entry_point () in
  A.Dom.get_cvalue_or_bottom (A.initial_state ~lib_entry)

(* Builds the Analyzer module corresponding to a given configuration,
   and sets it as the current analyzer. *)
let make_analyzer config =
  let analyzer =
    if Abstractions.Config.(equal config legacy) then (module Legacy: Analyzer)
    else if Abstractions.Config.(equal config default) then (module Default)
    else
      let module Abstract = (val Abstractions.make config) in
      let module Analyzer = Make (Abstract) in
      (module Analyzer)
  in
  set_current_analyzer config analyzer

(* Builds the analyzer according to the parameters of Eva. *)
let reset_analyzer () =
  let config = Abstractions.configure () in
  (* If the configuration has not changed, do not reset the Analyzer but uses
     the reference instead. *)
  if not (Abstractions.Config.equal config (fst !ref_analyzer))
  then make_analyzer config

(* Builds the analyzer if needed, and run the analysis. *)
let force_compute () =
  Ast.compute ();
  Parameters.configure_precision ();
  if not (Kernel.AuditCheck.is_empty ()) then
    Eva_audit.check_configuration (Kernel.AuditCheck.get ());
  let kf, lib_entry = Globals.entry_point () in
  reset_analyzer ();
  (* The new analyzer can be accesed through hooks *)
  Self.set_computation_state Computing;
  let module Analyzer = (val snd !ref_analyzer) in
  Analyzer.compute_from_entry_point ~lib_entry kf

let compute () =
  (* Nothing to recompute when Eva has already been computed. This boolean
      is automatically cleared when an option of Eva changes, because they
      are registered as dependencies on [Self.state] in {!Parameters}.*)
  if not (is_computed ()) then force_compute ()

let compute =
  let name = "Eva.Analysis.compute" in
  let f = Journal.register name  Datatype.(func unit unit) compute in
  fst (State_builder.apply_once name [ Self.state ] f)

(* Resets the Analyzer when the current project is changed. *)
let () =
  Project.register_after_set_current_hook
    ~user_only:true (fun _ -> reset_analyzer ());
  Project.register_after_global_load_hook reset_analyzer
