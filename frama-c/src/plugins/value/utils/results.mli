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

[@@@ api_start]

(** Eva's result API is a work-in-progress interface to allow accessing the
    analysis results once its completed. It is experimental and is very likely
    to change in the future. It aims at replacing [Db.Value] but does not
    completely covers all its usages yet. As for now, this interface has some
    advantages over Db's :

    - evaluations uses every available domains and not only Cvalue;
    - the caller may distinguish failure cases when a request is unsucessful;
    - working with callstacks is easy;
    - some common shortcuts are provided (e.g. for extracting ival directly);
    - overall, individual functions are simpler.

    The idea behind this API is that requests must be decomposed in several
    steps. For instance, to evaluate an expression :

    1. first, you have to state where you want to evaluate it,
    2. optionally, you may specify in which callstack,
    3. you choose the expression to evaluate,
    4. you require a destination type to evaluate into.

    Usage sketch :

    Eva.Results.(
      before stmt |> in_callstack cs |>
      eval_var vi |> as_int |> default 0)

    or equivalently, if you prefer

    Eva.Results.(
      default O (as_int (eval_var vi (in_callstack cs (before stmt))))
*)

(** Are results available for a given function? True if the function body has
    been has been analyzed and the results have been saved.
    False if:
    - the function has not been reached by the analysis: all requests in the
      function will lead to a Bottom error.
    - a specification or a builtin has been used instead of analyzing the
      function body: all requests in the function will lead to a Bottom error.
    - results have not been saved, due to the [-eva-no-results] parameter:
      all requests in the function will lead to a Top error. *)
val are_available: Cil_types.kernel_function -> bool

type callstack = (Cil_types.kernel_function * Cil_types.kinstr) list

type request

type value
type address
type 'a evaluation

type error = Bottom | Top | DisabledDomain
type 'a result = ('a,error) Result.t


(** Results handling *)

(** Translates an error to a human readable string. *)
val string_of_error : error -> string

(** Pretty printer for errors. *)
val pretty_error : Format.formatter -> error -> unit

(** Pretty printer for API's results. *)
val pretty_result : (Format.formatter -> 'a -> unit) ->
  Format.formatter -> 'a result -> unit

(** [default d r] extracts the value of [r] if [r] is Ok,
    or use the default value [d] otherwise.
    Equivalent to [Result.value ~default:d r] *)
val default : 'a -> 'a result -> 'a


(** Control point selection *)

(** At the start of the analysis, but after the initialization of globals. *)
val at_start : request

(** At the end of the analysis, after the main function has returned. *)
val at_end : unit -> request

(** At the start of the given function. *)
val at_start_of : Cil_types.kernel_function -> request

(** At the end of the given function.
    @raises Kernel_function.No_statement if the function has no body. *)
val at_end_of : Cil_types.kernel_function -> request

(** Just before a statement is executed. *)
val before : Cil_types.stmt -> request

(** Just after a statement is executed. *)
val after : Cil_types.stmt -> request

(** Just before a statement or at the start of the analysis. *)
val before_kinstr : Cil_types.kinstr -> request


(** Callstack selection *)

(** Only consider the given callstack.
    Replaces previous calls to [in_callstack] or [in_callstacks]. *)
val in_callstack : callstack -> request -> request

(** Only consider the callstacks from the given list.
    Replaces previous calls to [in_callstack] or [in_callstacks]. *)
val in_callstacks : callstack list -> request -> request

(** Only consider callstacks satisfying the given predicate. Several filters
    can be added. If callstacks are also selected with [in_callstack] or
    [in_callstacks], only the selected callstacks will be filtered. *)
val filter_callstack : (callstack -> bool) -> request -> request


(** Working with callstacks *)

(** Returns the list of reachable callstacks from the given request.
    An empty list is returned if the request control point has not been
    reached by the analysis, or if no information has been saved at this point
    (for instance with the -eva-no-results option).
    Use [is_empty request] to distinguish these two cases. *)
val callstacks : request -> callstack list

(** Returns a list of subrequests for each reachable callstack from
    the given request. *)
val by_callstack : request -> (callstack * request) list


(** State requests *)

(** Returns the list of expressions which have been inferred to be equal to
    the given expression by the Equality domain. *)
val equality_class : Cil_types.exp -> request -> Cil_types.exp list result

(** Returns the Cvalue state. Error cases are converted into the bottom or top
    cvalue state accordingly. *)
val get_cvalue_model : request -> Cvalue.Model.t

(** Returns the Cvalue model. *)
val get_cvalue_model_result : request -> Cvalue.Model.t result


(** Dependencies *)

(** Computes (an overapproximation of) the memory zones that must be read to
    evaluate the given expression, including all adresses computations. *)
val expr_deps : Cil_types.exp -> request -> Locations.Zone.t

(** Computes (an overapproximation of) the memory zones that must be read to
    evaluate the given lvalue, including the lvalue zone itself. *)
val lval_deps : Cil_types.lval -> request -> Locations.Zone.t

(** Computes (an overapproximation of) the memory zones that must be read to
    evaluate the given lvalue, excluding the lvalue zone itself. *)
val address_deps : Cil_types.lval -> request -> Locations.Zone.t


(** Evaluation *)

(** Returns (an overapproximation of) the possible values of the variable. *)
val eval_var : Cil_types.varinfo -> request -> value evaluation

(** Returns (an overapproximation of) the possible values of the lvalue. *)
val eval_lval : Cil_types.lval -> request -> value evaluation

(** Returns (an overapproximation of) the possible values of the expression. *)
val eval_exp : Cil_types.exp -> request -> value evaluation


(** Returns (an overapproximation of) the possible addresses of the lvalue. *)
val eval_address : ?for_writing:bool ->
  Cil_types.lval -> request -> address evaluation


(** Returns the kernel functions into which the given expression may evaluate.
    If the callee expression doesn't always evaluate to a function, those
    spurious values are ignored. If it always evaluate to a non-function value
    then the returned list is empty.
    Raises [Stdlib.Invalid_argument] if the callee expression is not an lvalue
    without offset.
    Also see [callee] for a function which applies directly on Call
    statements. *)
val eval_callee : Cil_types.exp -> request -> Kernel_function.t list result


(** Evaluated values conversion *)

(** In all functions below, if the abstract value inferred by Eva does not fit
    in the required type, [Error Top] is returned, as Top is the only possible
    over-approximation of the request. *)

(** Converts the value into a singleton ocaml int. *)
val as_int : value evaluation -> int result

(** Converts the value into a singleton unbounded integer. *)
val as_integer : value evaluation -> Integer.t result

(** Converts the value into a floating point number. *)
val as_float : value evaluation -> float result

(** Converts the value into a C number abstraction. *)
val as_ival : value evaluation -> Ival.t result

(** Converts the value into a floating point abstraction. *)
val as_fval : value evaluation -> Fval.t result

(** Converts the value into a Cvalue abstraction. Converts error cases
    into bottom and top values accordingly. *)
val as_cvalue : value evaluation -> Cvalue.V.t

(** Converts the value into a Cvalue abstraction. *)
val as_cvalue_result : value evaluation -> Cvalue.V.t result

(** Converts the value into a Cvalue abstraction with 'undefined' and 'escaping
    addresses' flags. *)
val as_cvalue_or_uninitialized : value evaluation -> Cvalue.V_Or_Uninitialized.t


(** Converts into a C location abstraction. *)
val as_location : address evaluation -> Locations.location result

(** Converts into a Zone. Error cases are converted into bottom or top zones
    accordingly. *)
val as_zone: address evaluation -> Locations.Zone.t

(** Converts into a Zone result. *)
val as_zone_result : address evaluation -> Locations.Zone.t result


(** Evaluation properties *)


(** Does the evaluated abstraction represents only one possible C value or
    memory location? *)
val is_singleton : 'a evaluation -> bool

(** Returns whether the evaluated value is initialized or not. If the value have
    been evaluated from a Cil expression, it is always initialized. *)
val is_initialized : value evaluation -> bool

(** Returns the set of alarms emitted during the evaluation. *)
val alarms : 'a evaluation -> Alarms.t list


(** Reachability *)

(** Returns true if there are no reachable states for the given request. *)
val is_empty : request -> bool

(** Returns true if an evaluation leads to bottom, i.e. if the given expression
    or lvalue cannot be evaluated to a valid result for the given request. *)
val is_bottom : 'a evaluation -> bool

(** Returns true if the function has been analyzed. *)
val is_called : Cil_types.kernel_function -> bool

(** Returns true if the statement has been reached by the analysis. *)
val is_reachable : Cil_types.stmt -> bool

(** Returns true if the statement has been reached by the analysis, or if
    the main function has been analyzed for [Kglobal]. *)
val is_reachable_kinstr : Cil_types.kinstr -> bool

val condition_truth_value: Cil_types.stmt -> bool * bool
(** Provided [stmt] is an 'if' construct, [fst (condition_truth_value stmt)]
    (resp. snd) is true if and only if the condition of the 'if' has been
    evaluated to true (resp. false) at least once during the analysis. *)

(*** Callers / Callees / Callsites *)

(** Returns the list of inferred callers of the given function. *)
val callers : Cil_types.kernel_function -> Cil_types.kernel_function list

(** Returns the list of inferred callers, and for each of them, the list
    of callsites (the call statements) inside. *)
val callsites : Cil_types.kernel_function ->
  (Cil_types.kernel_function * Cil_types.stmt list) list


(** Returns the kernel functions called in the given statement.
    If the callee expression doesn't always evaluate to a function, those
    spurious values are ignored. If it always evaluate to a non-function value
    then the returned list is empty.
    Raises [Stdlib.Invalid_argument] if the statement is not a [Call]
    instruction or a [Local_init] with [ConsInit] initializer. *)
val callee : Cil_types.stmt -> Kernel_function.t list

[@@@ api_end]
