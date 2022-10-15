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

open Lattice_bounds

let are_available kf =
  Analysis.is_computed () &&
  match Analysis.status kf with
  | Analyzed (Complete | Partial) -> true
  | SpecUsed | Builtin _ | Unreachable | Analyzed NoResults -> false

module Callstack = Value_types.Callstack

type callstack = Callstack.t
type 'a by_callstack = (callstack * 'a) list

type control_point =
  | Initial
  | Start of Cil_types.kernel_function
  | Before of Cil_types.stmt
  | After of Cil_types.stmt

type request = {
  control_point : control_point;
  selector : callstack list option;
  filter: (callstack -> bool) list;
}

type error = Bottom | Top | DisabledDomain
type 'a result = ('a,error) Result.t

let string_of_error = function
  | Bottom -> "The computed state is bottom"
  | Top -> "The computed state is Top"
  | DisabledDomain -> "The required domain is disabled"

let pretty_error fmt error =
  Format.pp_print_string fmt (string_of_error error)
let pretty_result f fmt r =
  Result.fold ~ok:(f fmt) ~error:(pretty_error fmt) r


(* Building requests *)

let make control_point = {
  control_point;
  selector = None;
  filter = [];
}

let before stmt = make (Before stmt)
let after stmt = make (After stmt)
let at_start_of kf = make (Start kf)
let at_end_of kf = make (After (Kernel_function.find_return kf))
let at_start = make Initial
let at_end () = at_end_of (fst (Globals.entry_point ()))

let before_kinstr = function
  | Cil_types.Kglobal -> at_start
  | Kstmt stmt -> before stmt

let in_callstacks l req = { req with selector = Some l }
let in_callstack cs req = { req with selector = Some [cs] }
let filter_callstack f req = { req with filter = f :: req.filter }


(* Manipulating request results *)

type restricted_to_callstack
type unrestricted_response

module Response =
struct

  type ('a, 'callstack) t =
    | Consolidated : 'a -> ('a, unrestricted_response) t
    | ByCallstack  : 'a by_callstack -> ('a, 'callstack) t
    | Top : ('a, 'callstack) t
    | Bottom : ('a, 'callstack) t

  let coercion : ('a, restricted_to_callstack) t -> ('a, 'c) t = function
    | ByCallstack c -> ByCallstack c
    | Top -> Top
    | Bottom -> Bottom

  let is_bottom = function
    | ByCallstack [] | Bottom -> true
    | _ -> false

  (* Constructors *)

  let consolidated ~top =
    function
    | `Bottom -> Bottom
    | `Top -> Consolidated top
    | `Value state -> Consolidated state

  let singleton cs =
    function
    | `Bottom -> Bottom
    | `Top -> Top
    | `Value state -> ByCallstack [cs,state]

  let by_callstack : request ->
    [< `Bottom | `Top | `Value of 'a Value_types.Callstack.Hashtbl.t ] ->
    ('a, restricted_to_callstack) t =
    fun req -> function
      | `Top -> Top
      | `Bottom -> Bottom
      | `Value table ->
        let add cs state acc =
          if List.for_all (fun filter -> filter cs) req.filter
          then (cs, state) :: acc
          else acc
        in
        let list = Callstack.Hashtbl.fold add table [] in
        ByCallstack list

  (* Accessors *)

  let callstacks : ('a, restricted_to_callstack) t -> callstack list = function
    | Top | Bottom -> [] (* What else to do when Top is given ? *)
    | ByCallstack l -> List.map fst l

  (* Fold *)

  let fold (f  : callstack -> 'a -> 'b -> 'b) (acc : 'b) :
    ('a, restricted_to_callstack) t -> 'b =
    function
    | Top | Bottom -> acc (* What else to do when Top is given ? *)
    | ByCallstack l -> List.fold_left (fun acc (cs,x) -> f cs x acc) acc l

  (* Map *)

  let map : type c. ('a -> 'b) -> ('a, c) t -> ('b, c) t = fun f -> function
    | Consolidated v -> Consolidated (f v)
    | ByCallstack l -> ByCallstack (List.map (fun (cs,x) -> cs,f x) l)
    | Top -> Top
    | Bottom -> Bottom

  (* Reduction *)

  let map_reduce : type c. ([`Top | `Bottom] -> 'b) -> ('a -> 'b) ->
    ('b -> 'b -> 'b) -> ('a, c) t -> 'b =
    fun default map reduce -> function
      | Consolidated v -> map v
      | ByCallstack ((_,h) :: t) ->
        List.fold_left (fun acc (_,x) -> reduce acc (map x)) (map h) t
      | ByCallstack [] | Bottom -> default `Bottom
      | Top -> default `Top

  let default = function
    | `Bottom -> `Bottom
    | `Top -> `Top

  let map_join : type c.
    ('a -> 'b) -> ('b -> 'b -> 'b) -> ('a, c) t -> 'b or_top_bottom =
    fun map join ->
    let map' x = `Value (map x)
    and join' = TopBottom.join (fun x y -> `Value (join x y)) in
    map_reduce default map' join'

  let map_join' : type c. ('a -> [< 'b or_top_bottom]) -> ('b -> 'b -> 'b) ->
    ('a, c) t -> 'b or_top_bottom =
    fun map join ->
    let join' = TopBottom.join (fun x y -> `Value (join x y)) in
    map_reduce default map join'
end


(* Extracting states and values *)

type value
type address

module Make () =
struct
  open TopBottom.Operators

  module A = (val Analysis.current_analyzer ())

  module EvalTypes =
  struct
    type valuation = A.Eval.Valuation.t
    type exp = (valuation * A.Val.t) Eval.evaluated
    type lval = (valuation * A.Val.t Eval.flagged_value) Eval.evaluated
    type loc = (valuation * A.Loc.location * Cil_types.typ) Eval.evaluated
  end

  type ('a,'c) evaluation =
    | LValue: (EvalTypes.lval, 'c) Response.t -> (value,'c) evaluation
    | Value: (EvalTypes.exp, 'c) Response.t -> (value,'c) evaluation
    | Address: (EvalTypes.loc, 'c) Response.t * Locations.access ->
        (address,'c) evaluation

  let get_by_callstack (req : request) :
    (_, restricted_to_callstack) Response.t =
    let open Response in
    let selection = req.selector in
    match req.control_point with
    | Before stmt ->
      A.get_stmt_state_by_callstack ?selection ~after:false stmt
      |> by_callstack req
    | After stmt ->
      A.get_stmt_state_by_callstack ?selection ~after:true stmt
      |> by_callstack req
    | Initial ->
      A.get_global_state () |> singleton []
    | Start kf ->
      A.get_initial_state_by_callstack ?selection kf |> by_callstack req

  let get (req : request) : (_, unrestricted_response) Response.t =
    if req.filter <> [] || Option.is_some req.selector then
      Response.coercion @@ get_by_callstack req
    else
      let open Response in
      let state =
        match req.control_point with
        | Before stmt -> A.get_stmt_state ~after:false stmt
        | After stmt -> A.get_stmt_state ~after:true stmt
        | Start kf -> A.get_initial_state kf
        | Initial -> A.get_global_state ()
      in
      consolidated ~top:A.Dom.top state

  let convert : 'a or_top_bottom -> 'a result = function
    | `Top -> Result.error Top
    | `Bottom -> Result.error Bottom
    | `Value v -> Result.ok v

  let callstacks req =
    get_by_callstack req |> Response.callstacks

  let by_callstack req =
    let f cs _res acc =
      (cs, in_callstack cs req) :: acc
    in
    get_by_callstack req |> Response.fold f []

  let is_reachable req =
    match get req with
    | Bottom -> false
    | _ -> true

  let equality_class exp req =
    let open Equality in
    match A.Dom.get Equality_domain.key with
    | None ->
      Result.error DisabledDomain
    | Some extract ->
      let hce = Hcexprs.HCE.of_exp exp in
      let extract' state =
        let equalities = Equality_domain.project (extract state) in
        try NonTrivial (Set.find hce equalities)
        with Not_found -> Trivial
      and reduce e1 e2 =
        match e1, e2 with
        | Trivial, _ | _, Trivial -> Trivial
        | NonTrivial e1, NonTrivial e2 -> Equality.inter e1 e2
      in
      let r = match Response.map_join extract' reduce (get req) with
        | (`Top | `Bottom) as r -> r
        | `Value Trivial -> `Top
        | `Value (NonTrivial e) ->
          let l = Equality.elements e in
          `Value (List.map Hcexprs.HCE.to_exp l)
      in
      convert r

  let get_cvalue_model req =
    match A.Dom.get_cvalue with
    | None ->
      Result.error DisabledDomain
    | Some extract ->
      convert (Response.map_join extract Cvalue.Model.join (get req))

  (* Evaluation *)

  let eval_lval lval req =
    let eval state = A.Eval.copy_lvalue state lval in
    LValue (Response.map eval (get req))

  let eval_exp exp req =
    let eval state = A.Eval.evaluate state exp in
    Value (Response.map eval (get req))

  let eval_address ~for_writing lval req =
    let eval state = A.Eval.lvaluate ~for_writing state lval in
    let access = if for_writing then Locations.Write else Read in
    Address (Response.map eval (get req), access)

  let eval_callee exp req =
    let join = (@)
    and extract state =
      let r,_alarms = A.Eval.eval_function_exp exp state in
      r >>-: List.map fst
    in
    get req |> Response.map_join' extract join |> convert |>
    Result.map (List.sort_uniq Kernel_function.compare)


  (* Conversion *)

  let as_cvalue_or_uninitialized res =
    match A.Val.get Main_values.CVal.key with
    | None -> `Top
    | Some get ->
      let make_expr (x, _alarms) =
        x >>-: fun (_valuation, v) ->
        Cvalue.V_Or_Uninitialized.make ~initialized:true ~escaping:false (get v)
      in
      let make_lval (x, _alarms) =
        let+ _valuation, v = x in
        let Eval.{ v; initialized; escaping } = v in
        let v =
          match v with
          | `Bottom -> Cvalue.V.bottom
          | `Value v -> get v
        in
        Cvalue.V_Or_Uninitialized.make ~initialized ~escaping v
      in
      let join = Cvalue.V_Or_Uninitialized.join in
      match res with
      | LValue r -> Response.map_join' make_lval join r
      | Value r -> Response.map_join' make_expr join r

  let extract_value :
    type c. (value, c) evaluation -> (A.Val.t or_bottom, c) Response.t =
    let open Bottom.Operators in
    function
    | LValue r ->
      let extract (x, _alarms) = x >>- (fun (_valuation,fv) -> fv.Eval.v) in
      Response.map extract r
    | Value r ->
      let extract (x, _alarms) = x >>-: (fun (_valuation,v) -> v) in
      Response.map extract r

  let as_cvalue res =
    match A.Val.get Main_values.CVal.key with
    | None ->
      Result.error DisabledDomain
    | Some get ->
      let join = Main_values.CVal.join in
      let extract value =
        value >>-: get
      in
      extract_value res |> Response.map_join' extract join |> convert

  let extract_loc :
    type c. (address, c) evaluation ->
    (A.Loc.location or_bottom, c) Response.t * Locations.access =
    function
    | Address (r, access) ->
      let extract (x, _alarms) =
        let open Bottom.Operators in
        let+ _valuation,loc,_typ = x in loc
      in
      Response.map extract r, access

  let as_location res =
    match A.Loc.get Main_locations.PLoc.key with
    | None ->
      Result.error DisabledDomain
    | Some get ->
      let join loc1 loc2 =
        let open Locations in
        let size = loc1.size
        and loc = Location_Bits.join loc1.loc loc2.loc in
        assert (Int_Base.equal loc2.size size);
        make_loc loc size
      and extract loc =
        loc >>-: get >>-: Precise_locs.imprecise_location
      in
      extract_loc res |> fst |> Response.map_join' extract join |> convert

  let as_zone res =
    match A.Loc.get Main_locations.PLoc.key with
    | None ->
      Result.error DisabledDomain
    | Some get ->
      let response_loc, access = extract_loc res in
      let join = Locations.Zone.join
      and extract loc =
        loc >>-: get >>-:
        Precise_locs.enumerate_valid_bits access
      in
      response_loc |> Response.map_join' extract join |> convert

  let is_initialized : type c. (value,c) evaluation -> bool =
    function
    | LValue r ->
      let join = (&&)
      and extract (x, _alarms) =
        x >>-: (fun (_valuation,fv) -> fv.Eval.initialized)
      in
      begin match Response.map_join' extract join r with
        | `Bottom | `Top -> false
        | `Value v -> v
      end
    | Value _ -> true (* computed values are always initialized *)

  let alarms : type a c. (a,c) evaluation -> Alarms.t list =
    fun res ->
    let extract (_,v) = `Value v in
    let r = match res with
      | LValue r ->
        Response.map_join' extract Alarmset.union r
      | Value r ->
        Response.map_join' extract Alarmset.union r
      | Address (r, _lval) ->
        Response.map_join' extract Alarmset.union r
    in
    match r with
    | `Bottom | `Top -> []
    | `Value alarmset ->
      let add alarm status acc =
        if status <> Alarmset.True then alarm :: acc else acc
      in
      Alarmset.fold add [] alarmset

  let is_bottom : type a c. (a,c) evaluation -> bool = function
    | LValue r -> Response.is_bottom r
    | Value r -> Response.is_bottom r
    | Address (r, _lval) -> Response.is_bottom r

  (* Dependencies *)

  let compute_deps eval_deps arg req =
    let error = function
      | Bottom -> Locations.Zone.bottom
      | Top | DisabledDomain -> Locations.Zone.top
    in
    let compute cvalue =
      eval_deps (cvalue, Locals_scoping.bottom ()) arg
    in
    req |> get_cvalue_model |> Result.fold ~error ~ok:compute

  let lval_deps = compute_deps Register.eval_deps_lval
  let expr_deps = compute_deps Register.eval_deps
  let address_deps = compute_deps Register.eval_deps_addr
end


(* Working with callstacks *)

let callstacks req =
  let module E = Make () in
  E.callstacks req

let by_callstack req =
  let module E = Make () in
  E.by_callstack req


(* State requests *)

let equality_class exp req =
  let module E = Make () in
  E.equality_class exp req

let get_cvalue_model_result req =
  let module E = Make () in
  E.get_cvalue_model req

let get_cvalue_model req =
  match get_cvalue_model_result req with
  | Ok state -> state
  | Error Bottom -> Cvalue.Model.bottom
  | Error (Top | DisabledDomain) -> Cvalue.Model.top


(* Depedencies *)

let expr_deps exp req =
  let module E = Make () in
  E.expr_deps exp req

let lval_deps lval req =
  let module E = Make () in
  E.lval_deps lval req

let address_deps lval req =
  let module E = Make () in
  E.address_deps lval req


(* Evaluation *)

module type Lvaluation =
sig
  include module type of (Make ())
  val v : (address, unrestricted_response) evaluation
end

module type Evaluation =
sig
  include module type of (Make ())
  val v : (value, unrestricted_response) evaluation
end

type 'a evaluation =
  | Value: (module Evaluation) -> value evaluation
  | Address: (module Lvaluation) -> address evaluation

let build_eval_lval_and_exp () =
  let module M = Make () in
  let build v =
    (module struct
      include M
      let v = v
    end : Evaluation)
  in
  let eval_lval lval req = build @@ M.eval_lval lval req in
  let eval_exp exp req = build @@ M.eval_exp exp req in
  eval_lval, eval_exp

let eval_lval lval req = Value ((fst @@ build_eval_lval_and_exp ()) lval req)

let eval_var vi req = eval_lval (Cil.var vi) req

let eval_exp exp req = Value ((snd @@ build_eval_lval_and_exp ()) exp req)

let eval_address ?(for_writing=false) lval req =
  let module M = Make () in
  let v = M.eval_address ~for_writing lval req in
  Address
    (module struct
      include M
      let v = v
    end : Lvaluation)

let eval_callee exp req =
  (* Check the validity of exp *)
  begin match exp with
    | Cil_types.({ enode = Lval (_, NoOffset) }) -> ()
    | _ ->
      invalid_arg "The callee must be an lvalue with no offset"
  end;
  let module M = Make () in
  M.eval_callee exp req

let callee stmt =
  let callee_exp =
    match stmt.Cil_types.skind with
    | Instr (Call (_lval, callee_exp, _args, _loc)) ->
      callee_exp
    | Instr (Local_init (_vi, ConsInit (f, _, _), _loc)) ->
      Cil.evar f
    | _ ->
      invalid_arg "Can only evaluate the callee on a statement which is a Call"
  in
  before stmt |> eval_callee callee_exp |> Result.value ~default:[]

(* Value conversion *)

let as_cvalue_or_uninitialized (Value evaluation) =
  let module E = (val evaluation : Evaluation) in
  match E.as_cvalue_or_uninitialized E.v with
  | `Value v -> v
  | `Bottom -> Cvalue.V_Or_Uninitialized.bottom
  | `Top -> Cvalue.V_Or_Uninitialized.top

let as_cvalue_result (Value evaluation) =
  let module E = (val evaluation : Evaluation) in
  E.as_cvalue E.v

let as_cvalue evaluation =
  match as_cvalue_result evaluation with
  | Ok v -> v
  | Error Bottom -> Cvalue.V.bottom
  | Error (Top | DisabledDomain) -> Cvalue.V.top

let as_ival evaluation =
  try
    Result.map Cvalue.V.project_ival (as_cvalue_result evaluation)
  with Cvalue.V.Not_based_on_null ->
    Result.error Top

let as_fval evaluation =
  let f ival =
    if Ival.is_float ival
    then Result.ok (Ival.project_float ival)
    else Result.error Top
  in
  Result.bind (as_ival evaluation) f

let as_float evaluation =
  try
    as_fval evaluation |>
    Result.map Fval.project_float |>
    Result.map Fval.F.to_float
  with Fval.Not_Singleton_Float ->
    Result.error Top

let as_integer evaluation =
  try
    Result.map Ival.project_int (as_ival evaluation)
  with Ival.Not_Singleton_Int ->
    Result.error Top

let as_int evaluation =
  try
    Result.map Integer.to_int_exn (as_integer evaluation)
  with Z.Overflow ->
    Result.error Top

let as_location (Address lvaluation) =
  let module E = (val lvaluation : Lvaluation) in
  E.as_location E.v

let as_zone_result (Address lvaluation) =
  let module E = (val lvaluation : Lvaluation) in
  E.as_zone E.v

let as_zone address =
  match as_zone_result address with
  | Ok zone -> zone
  | Error Bottom -> Locations.Zone.bottom
  | Error (Top | DisabledDomain) -> Locations.Zone.top

(* Evaluation properties *)

let is_singleton: type a. a evaluation -> bool = function
  | Value _ as evaluation ->
    let cvalue = as_cvalue evaluation in
    Cvalue.V.cardinal_zero_or_one cvalue && not (Cvalue.V.is_bottom cvalue)
  | Address _ as lvaluation ->
    let loc = as_location lvaluation in
    let is_singleton loc =
      Locations.cardinal_zero_or_one loc && not (Locations.is_bottom_loc loc)
    in
    Result.fold ~ok:is_singleton ~error:(fun _ -> false) loc

let is_initialized (Value evaluation) =
  let module E = (val evaluation : Evaluation) in
  E.is_initialized E.v

let alarms : type a. a evaluation -> Alarms.t list =
  function
  | Value evaluation ->
    let module E = (val evaluation : Evaluation) in
    E.alarms E.v
  | Address lvaluation ->
    let module L = (val lvaluation : Lvaluation) in
    L.alarms L.v

(* Reachability *)

let is_empty rq =
  let module E = Make () in
  E.callstacks rq = []

let is_bottom : type a. a evaluation -> bool =
  function
  | Value evaluation ->
    let module E = (val evaluation : Evaluation) in
    E.is_bottom E.v
  | Address lvaluation ->
    let module L = (val lvaluation : Lvaluation) in
    L.is_bottom L.v

let is_reachable stmt =
  let module M = Make () in
  M.is_reachable (before stmt)

let is_reachable_kinstr kinstr =
  let module M = Make () in
  M.is_reachable (before_kinstr kinstr)

let condition_truth_value = Db.Value.condition_truth_value

(* Callers / callsites *)

let is_called = Function_calls.is_called
let callers = Function_calls.callers
let callsites = Function_calls.callsites

(* Result conversion *)

let default default_value result =
  Result.value ~default:default_value result
