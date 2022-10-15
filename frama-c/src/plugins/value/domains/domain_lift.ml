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

open Eval

module type Conversion = sig
  type extended_value
  type extended_location
  type internal_value
  type internal_location

  val extend_val : internal_value -> extended_value
  val restrict_val : extended_value -> internal_value

  val extend_loc : internal_location -> extended_location
  val restrict_loc : extended_location -> internal_location
end


module Make
    (Domain: Abstract_domain.Leaf)
    (Convert : Conversion with type internal_value := Domain.value
                           and type internal_location := Domain.location)
= struct

  include (Domain : Datatype.S_with_collections with type t = Domain.t)
  include (Domain : Abstract_domain.Lattice with type state = Domain.state)

  let structure = Abstract.Domain.Leaf (Domain.key, (module Domain))

  let log_category = Domain.log_category

  type value = Convert.extended_value
  type location = Convert.extended_location
  type origin = Domain.origin

  let extract_expr ~oracle context state exp =
    let oracle exp = oracle exp >>=: Convert.restrict_val in
    Domain.extract_expr ~oracle context state exp >>=: fun (value, origin) ->
    Convert.extend_val value, origin

  let extract_lval ~oracle context state lval typ loc =
    let oracle exp = oracle exp >>=: Convert.restrict_val in
    let loc = Convert.restrict_loc loc in
    Domain.extract_lval ~oracle context state lval typ loc
    >>=: fun (value, origin) ->
    Convert.extend_val value, origin

  let backward_location state lval typ loc value =
    Domain.backward_location
      state lval typ (Convert.restrict_loc loc) (Convert.restrict_val value)
    >>-: fun (loc, value) ->
    Convert.extend_loc loc, Convert.extend_val value

  let reduce_further state expr value =
    let list = Domain.reduce_further state expr (Convert.restrict_val value) in
    List.map (fun (e, v) -> e, Convert.extend_val v) list


  let lift_left left = { left with lloc = Convert.restrict_loc left.lloc }
  let lift_flagged_value value =
    { value with v = value.v >>-: Convert.restrict_val }
  let lift_assigned = function
    | Assign value -> Assign (Convert.restrict_val value)
    | Copy (lval, value) -> Copy (lift_left lval, lift_flagged_value value)

  let lift_argument arg = { arg with avalue = lift_assigned arg.avalue }

  let lift_call call =
    let arguments = List.map lift_argument call.arguments in
    let rest =
      List.map (fun (exp, assigned) -> exp, lift_assigned assigned) call.rest
    in
    { call with arguments; rest }

  let lift_valuation valuation =
    let (>>>) v f = match v with
      | `Value v -> `Value (f v)
      | `Top -> `Top
    in
    let lift_record r = { r with value = lift_flagged_value r.value } in
    let lift_loc_record r = { r with loc = Convert.restrict_loc r.loc } in
    let open Abstract_domain in
    let find expr = valuation.find expr >>> lift_record in
    let find_loc lval = valuation.find_loc lval >>> lift_loc_record in
    let fold f acc =
      valuation.fold (fun exp record acc -> f exp (lift_record record) acc) acc
    in
    { find; fold; find_loc; }

  let update valuation = Domain.update (lift_valuation valuation)

  let assign stmt lv expr value valuation state =
    Domain.assign stmt
      (lift_left lv) expr (lift_assigned value) (lift_valuation valuation) state

  let assume stmt expr positive valuation state =
    Domain.assume stmt expr positive (lift_valuation valuation) state

  let start_call stmt call recursion valuation state =
    Domain.start_call
      stmt (lift_call call) recursion (lift_valuation valuation) state

  let finalize_call stmt call recursion ~pre ~post =
    Domain.finalize_call stmt (lift_call call) recursion ~pre ~post

  let show_expr valuation = Domain.show_expr (lift_valuation valuation)

  let lift_logic_dep dep =
    let location = Option.map Convert.restrict_loc dep.location in
    { dep with location }

  let lift_logic_assigns = function
    | Assigns (term, dep) -> Assigns (term, List.map lift_logic_dep dep)
    | (Allocates _ | Frees _) as x -> x

  let logic_assign assigns location state =
    let assigns = Option.map (fun (a, s) -> lift_logic_assigns a, s) assigns in
    Domain.logic_assign assigns (Convert.restrict_loc location) state

  let evaluate_predicate = Domain.evaluate_predicate
  let reduce_by_predicate = Domain.reduce_by_predicate
  let interpret_acsl_extension = Domain.interpret_acsl_extension

  let enter_scope = Domain.enter_scope
  let leave_scope = Domain.leave_scope

  let enter_loop = Domain.enter_loop
  let incr_loop_counter = Domain.incr_loop_counter
  let leave_loop = Domain.leave_loop

  let empty = Domain.empty
  let initialize_variable lval loc ~initialized init_value state =
    let loc = Convert.restrict_loc loc in
    Domain.initialize_variable lval loc ~initialized init_value state
  let initialize_variable_using_type = Domain.initialize_variable_using_type

  let relate = Domain.relate
  let filter = Domain.filter
  let reuse = Domain.reuse

  module Store = Domain.Store

  let post_analysis = Domain.post_analysis

end


(*
Local Variables:
compile-command: "make -C ../../../.."
End:
*)
