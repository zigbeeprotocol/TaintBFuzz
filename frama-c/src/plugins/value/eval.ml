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

(** *)

(* -------------------------------------------------------------------------- *)
(**                       {2 Lattice structure }                              *)
(* -------------------------------------------------------------------------- *)

include Lattice_bounds
include Bottom.Operators


(* -------------------------------------------------------------------------- *)
(**                     {2 Types for the evaluations }                        *)
(* -------------------------------------------------------------------------- *)

(* Forward evaluation. *)
type 't with_alarms = 't * Alarmset.t
type 't evaluated = 't or_bottom with_alarms

(* This monad propagates the `Bottom value if needed and join the potential
   alarms returned during the evaluation. *)
let (>>=) (t, a) f = match t with
  | `Bottom  -> `Bottom, a
  | `Value t -> let t', a' = f t in t', Alarmset.combine a a'

(* Use this monad if the following function returns a simple value. *)
let (>>=:) (t, a) f = match t with
  | `Bottom  -> `Bottom, a
  | `Value t -> let t' = f t in `Value t', a

(* Use this monad if the following function returns no alarms. *)
let (>>=.) (t, a) f = match t with
  | `Bottom  -> `Bottom, a
  | `Value t -> let t' = f t in t', a

(* Backward evaluation. *)
type 'a reduced = [ `Bottom | `Unreduced | `Value of 'a ]

(* -------------------------------------------------------------------------- *)
(**                     {2 Cache for the evaluations }                        *)
(* -------------------------------------------------------------------------- *)

(* State of the reduction of an abstract value. *)
type reductness =
  | Unreduced  (* No reduction. *)
  | Reduced    (* A reduction has been performed for this expression. *)
  | Created    (* The abstract value has been created. *)
  | Dull       (* Reduction is pointless for this expression. *)

(* Right values with 'undefined' and 'escaping addresses' flags. *)
type 'a flagged_value = {
  v: 'a or_bottom;
  initialized: bool;
  escaping: bool;
}

module Flagged_Value = struct

  let bottom = {v = `Bottom; initialized=true; escaping=false; }
  let equal equal v1 v2  =
    Bottom.equal equal v1.v v2.v &&
    v1.initialized = v2.initialized && v1.escaping = v2.escaping
  let join join v1 v2 =
    { v = Bottom.join join v1.v v2.v;
      initialized = v1.initialized && v2.initialized;
      escaping = v1.escaping || v2.escaping }

  let pretty_flags fmt value = match value.initialized, value.escaping with
    | false, true  -> Format.pp_print_string fmt "UNINITIALIZED or ESCAPINGADDR"
    | false, false -> Format.pp_print_string fmt "UNINITIALIZED"
    | true, true   -> Format.pp_print_string fmt "ESCAPINGADDR"
    | true, false  -> Format.pp_print_string fmt "BOTTOM"

  let pretty pp fmt value = match value.v with
    | `Bottom -> pretty_flags fmt value
    | `Value v ->
      if value.initialized && not value.escaping
      then pp fmt v
      else Format.fprintf fmt "%a or %a" pp v pretty_flags value

end

(* Data record associated to each evaluated expression. *)
type ('a, 'origin) record_val = {
  value : 'a flagged_value;  (* The resulting abstract value *)
  origin: 'origin option;   (* The origin of the abstract value *)
  reductness : reductness;  (* The state of reduction. *)
  val_alarms : Alarmset.t   (* The emitted alarms during the evaluation. *)
}

(* Data record associated to each evaluated left-value. *)
type 'a record_loc = {
  loc: 'a;                  (* The location of the left-value. *)
  typ: typ;                 (* *)
  loc_alarms: Alarmset.t    (* The emitted alarms during the evaluation. *)
}

(* Results of an evaluation: the results of all intermediate calculation (the
    value of each expression and the location of each lvalue) are cached in a
    map. *)
module type Valuation = sig
  type t
  type value  (* Abstract value. *)
  type origin (* Origin of values. *)
  type loc    (* Abstract memory location. *)

  val empty : t
  val find : t -> exp -> (value, origin) record_val or_top
  val add : t -> exp -> (value, origin) record_val -> t
  val fold : (exp -> (value, origin) record_val -> 'a -> 'a) -> t -> 'a -> 'a
  val find_loc : t -> lval -> loc record_loc or_top
  val remove : t -> exp -> t
  val remove_loc : t -> lval -> t
end

(* Returns the list of the subexpressions of [expr] that contain [subexpr],
   without [subexpr] itself. *)
let compute_englobing_subexpr ~subexpr ~expr =
  let merge = Extlib.merge_opt (fun _ -> (@)) () in
  (* Returns [Some] of the list of subexpressions of [expr] that contain
     [subexpr], apart [subexpr] itself, or [None] if [subexpr] does not appear
     in [expr]. *)
  let rec compute expr =
    if Cil_datatype.ExpStructEq.equal expr subexpr
    then Some []
    else
      let sublist = match expr.enode with
        | UnOp (_, e, _)
        | CastE (_, e) ->
          compute e
        | BinOp (_, e1, e2, _) ->
          merge (compute e1) (compute e2)
        | Lval (host, offset) ->
          merge (compute_host host) (compute_offset offset)
        | _ -> None
      in
      Option.map (fun l -> expr :: l) sublist
  and compute_host = function
    | Var _ -> None
    | Mem e -> compute e
  and compute_offset offset = match offset with
    | NoOffset -> None
    | Field (_, offset) -> compute_offset offset
    | Index (index, offset) ->
      merge (compute index) (compute_offset offset)
  in
  Option.value ~default:[] (compute expr)

module Englobing =
  Datatype.Pair_with_collections (Cil_datatype.ExpStructEq) (Cil_datatype.ExpStructEq)
    (struct  let module_name = "Subexpressions" end)
module SubExprs = Datatype.List (Cil_datatype.Exp)

module EnglobingSubexpr =
  State_builder.Hashtbl (Englobing.Hashtbl) (SubExprs)
    (struct
      let name = "Value.Eval.Englobing_subexpressions"
      let size = 32
      let dependencies = [ Ast.self ]
    end)

let compute_englobing_subexpr ~subexpr ~expr=
  EnglobingSubexpr.memo
    (fun (expr, subexpr) -> compute_englobing_subexpr ~subexpr ~expr)
    (expr, subexpr)

module Clear_Valuation (Valuation : Valuation) = struct
  let clear_englobing_exprs valuation ~expr ~subexpr =
    let englobing = compute_englobing_subexpr ~subexpr ~expr in
    let remove valuation expr =
      let valuation = Valuation.remove valuation expr in
      match expr.enode with
      | Lval lval -> Valuation.remove_loc valuation lval
      | _ -> valuation
    in
    List.fold_left remove valuation englobing
end


(* -------------------------------------------------------------------------- *)
(**                        {2 Types of assignments }                          *)
(* -------------------------------------------------------------------------- *)

type 'loc left_value = {
  lval: lval;
  lloc: 'loc;
  ltyp: typ;
}

(* Assigned values. *)
type ('loc, 'value) assigned =
  | Assign of 'value
  | Copy of 'loc left_value * 'value flagged_value

let value_assigned = function
  | Assign v -> `Value v
  | Copy (_, copied) -> copied.v

type 'location logic_dependency =
  { term: identified_term;
    direct: bool;
    location: 'location option; }

type 'location logic_assign =
  | Assigns of identified_term * 'location logic_dependency list
  | Allocates of identified_term
  | Frees of identified_term

(* -------------------------------------------------------------------------- *)
(**                       {2 Interprocedural Analysis }                       *)
(* -------------------------------------------------------------------------- *)

type ('loc, 'value) argument = {
  formal: varinfo;
  concrete: exp;
  avalue: ('loc, 'value) assigned;
}


type call_site = kernel_function * kinstr
type callstack = call_site list

type ('loc, 'value) call = {
  kf: kernel_function;
  callstack: callstack;
  arguments: ('loc, 'value) argument list;
  rest: (exp * ('loc, 'value) assigned) list;
  return: varinfo option;
}

type recursion = {
  depth: int;
  substitution: (varinfo * varinfo) list;
  base_substitution: Base.substitution;
  withdrawal: varinfo list;
  base_withdrawal: Base.Hptset.t;
}

type cacheable = Cacheable | NoCache | NoCacheCallers

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
