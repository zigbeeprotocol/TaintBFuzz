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
open Bottom.Operators

(* --- Split monitors --- *)

type split_monitor = {
  split_limit : int;
  mutable split_values : Datatype.Integer.Set.t;
}

let new_monitor ~split_limit = {
  split_limit;
  split_values = Datatype.Integer.Set.empty;
}

module SplitMonitor = Datatype.Make_with_collections (
  struct
    include Datatype.Serializable_undefined
    module Values = Datatype.Integer.Set

    type t = split_monitor

    let name = "Partition.SplitMonitor"

    let reprs = [ new_monitor ~split_limit:0 ]

    let structural_descr =
      Structural_descr.t_record
        [| Datatype.Int.packed_descr; Values.packed_descr |]

    let compare m1 m2 =
      let c = Int.compare m1.split_limit m2.split_limit in
      if c <> 0 then c else Values.compare m1.split_values m2.split_values

    let equal = Datatype.from_compare

    let pretty fmt m =
      Format.fprintf fmt "%d/%d" (Values.cardinal m.split_values) m.split_limit

    let hash m =
      hash (Datatype.Int.hash m.split_limit, Values.hash m.split_values)

    let copy m =
      { m with split_values = m.split_values }
  end)

(* --- Stamp rationing --- *)

(* Stamps used to label states according to slevel.
   The second integer is used to keep separate the different states resulting
   from a transfer function producing a state list before a new stamping.  *)
type stamp = (int * int) option (* store stamp / transfer stamp *)

(* Stamp rationing according to the slevel. *)
type rationing =
  { current: int ref; (* last used stamp. *)
    limit: int;       (* limit of available stamps; after, stamps are [None]. *)
    merge: bool       (* on merge slevel annotations or -eva-merge-after-loop,
                         merge the incoming states with one unique stamp. *)
  }

let new_rationing ~limit ~merge = { current = ref 0; limit; merge }

(* --- Keys --- *)

type split_term = Eva_annotations.split_term =
  | Expression of Cil_types.exp
  | Predicate of Cil_types.predicate

module SplitTerm = Datatype.Make_with_collections (struct
    include Datatype.Serializable_undefined

    module Expressions = Cil_datatype.ExpStructEq
    module Predicates = Cil_datatype.PredicateStructEq

    type t = split_term

    let name = "Partition.SplitTerm"

    let reprs =
      Stdlib.List.map (fun e -> Expression e) Expressions.reprs @
      Stdlib.List.map (fun p -> Predicate p) Predicates.reprs

    let structural_descr =
      Structural_descr.t_sum [|
        [| Expressions.packed_descr |] ;
        [| Predicates.packed_descr |] |]

    let compare x y =
      match x, y with
      | Expression e1, Expression e2 -> Expressions.compare e1 e2
      | Predicate p1, Predicate p2 -> Logic_utils.compare_predicate p1 p2
      | Expression _, Predicate _ -> 1
      | Predicate _, Expression _ -> -1

    let equal = Datatype.from_compare

    let pretty fmt = function
      | Expression e -> Printer.pp_exp fmt e
      | Predicate p -> Printer.pp_predicate fmt p

    let hash = function
      | Expression e -> FCHashtbl.hash (1,Expressions.hash e)
      | Predicate p -> FCHashtbl.hash (2,Predicates.hash p)
  end)

module SplitMap = SplitTerm.Map

type branch = int

(* The key have several fields, one for each kind of partitioning:
   - Ration stamps: These modelize the legacy slevel. Each state is given
     a ration stamp (represented by two integers) until there is no slevel
     left. The first number is attributed by the store it comes from, the
     second one is attributed by the last transfer.
     It is an option type, when there is no more ration stamp, this field is
     set to None; each new state will not be distinguished by this field.
   - Branches: This field enumerate the last junctions points passed through.
     The partitioning may chose how the branches are identified, but it
     is a First-In-First-Out set.
   - Loops: This field stores the loop iterations needed to reach this state
     for each loop we are currently in. It is stored in reverse order
     (innermost loop first) It also stores the maximum number of unrolling ;
     this number varies from a state to another, as it is computed from
     an expression evaluated when we enter the loop.
   - Splits: track the splits applied to the state as a map from the term of
     the split to its value. Terms can be C expresssions or ACSL predicates.
     Since the split creates states in which the expression evalutates to a
     singleton, the values of the map are integers.
     Static splits are only evaluated when the annotation is encountered
     whereas dynamic splits are reevaluated regularly; a list of active
     dynamic splits is also propagated in the key. *)
type key = {
  ration_stamp : stamp;
  branches : branch list;
  loops : (int * int) list; (* current iteration / max unrolling *)
  splits : Integer.t SplitMap.t; (* term -> value *)
  dynamic_splits : split_monitor SplitMap.t; (* term -> monitor *)
}

type call_return_policy = {
  callee_splits: bool;
  callee_history: bool;
  caller_history: bool;
  history_size: int;
}

module Key =
struct

  module IntPair = Datatype.Pair (Datatype.Int) (Datatype.Int)
  module Stamp = Datatype.Option (IntPair)
  module BranchList = Datatype.List (Datatype.Int)
  module LoopList = Datatype.List (IntPair)
  module Splits = SplitMap.Make (Datatype.Integer)
  module DSplits = SplitMap.Make (SplitMonitor)

  (* Initial key, before any partitioning *)
  let empty = {
    ration_stamp = None;
    branches = [];
    loops = [];
    splits = SplitMap.empty;
    dynamic_splits = SplitMap.empty;
  }

  include Datatype.Make_with_collections (struct
      include Datatype.Serializable_undefined

      type t = key

      let name = "Partition.Key"

      let reprs = [ empty ]

      let structural_descr =
        Structural_descr.t_record [|
          Stamp.packed_descr;
          BranchList.packed_descr;
          LoopList.packed_descr;
          Splits.packed_descr;
          DSplits.packed_descr;
        |]

      let compare k1 k2 =
        let (<?>) c (cmp,x,y) =
          if c = 0 then cmp x y else c
        in
        Stdlib.Option.compare IntPair.compare k1.ration_stamp k2.ration_stamp
        <?> (LoopList.compare, k1.loops, k2.loops)
        <?> (Splits.compare, k1.splits, k2.splits)
        (* Ignore monitors in comparison *)
        <?> (SplitMap.compare (fun _ _ -> 0), k1.dynamic_splits, k2.dynamic_splits)
        <?> (BranchList.compare, k1.branches, k2.branches)

      let equal = Datatype.from_compare

      let hash k =
        Stdlib.Hashtbl.hash (
          Stamp.hash k.ration_stamp,
          BranchList.hash k.branches,
          LoopList.hash k.loops,
          Splits.hash k.splits,
          DSplits.hash k.dynamic_splits) (* Monitors probably shouldn't be hashed *)

      let pretty fmt key =
        begin match key.ration_stamp with
          | Some (n,_) -> Format.fprintf fmt "#%d" n
          | None -> ()
        end;
        Pretty_utils.pp_list ~pre:"[@[" ~sep:" ;@ " ~suf:"@]]"
          Format.pp_print_int
          fmt
          key.branches;
        Pretty_utils.pp_list ~pre:"(@[" ~sep:" ;@ " ~suf:"@])"
          (fun fmt (i,_j) -> Format.pp_print_int fmt i)
          fmt
          key.loops;
        Pretty_utils.pp_list ~pre:"{@[" ~sep:" ;@ " ~suf:"@]}"
          (fun fmt (t, i) -> Format.fprintf fmt "%a:%a"
              SplitTerm.pretty t
              Datatype.Integer.pretty i)
          fmt
          (SplitMap.bindings key.splits)
    end)

  let exceed_rationing key = key.ration_stamp = None

  let combine ~policy ~caller ~callee =
    let keep_second _ v1 v2 =
      match v1, v2 with
      | None, None -> None
      | Some x, None | (Some _ | None), Some x -> Some x
    in
    (* There is no need to preserve the uniqueness of ration stamps here, as
       keys will always be given new stamps before the merge of identical keys.
       This invariant depends on the sequence of operations performed by
       the iterator and the trace_partitioning. *)
    {
      ration_stamp = None;
      branches =
        Extlib.list_first_n policy.history_size (
          (if policy.callee_history then callee.branches else []) @
          (if policy.caller_history then caller.branches else [])
        );
      loops = caller.loops;
      splits =
        if policy.callee_splits
        then SplitMap.merge keep_second caller.splits callee.splits
        else caller.splits;
      dynamic_splits =
        if policy.callee_splits
        then SplitMap.merge keep_second caller.dynamic_splits callee.dynamic_splits
        else caller.dynamic_splits;
    }
end


(* --- Partitions --- *)

module KMap = Key.Map

type 'a partition = 'a KMap.t

let empty = KMap.empty
let find = KMap.find
let replace = KMap.add
let is_empty = KMap.is_empty
let size = KMap.cardinal
let iter = KMap.iter
let map = KMap.map
let filter = KMap.filter
let merge = KMap.merge

let to_list (p : 'a partition) : (key * 'a) list =
  KMap.fold (fun k x l -> (k, x) :: l) p []


(* --- Partitioning actions --- *)

type unroll_limit =
  | ExpLimit of Cil_types.exp
  | IntLimit of int
  | AutoUnroll of Cil_types.stmt * int * int

type split_kind = Eva_annotations.split_kind = Static | Dynamic

type action =
  | Enter_loop of unroll_limit
  | Leave_loop
  | Incr_loop
  | Branch of branch * int
  | Ration of rationing
  | Restrict of Cil_types.exp * Integer.t list
  | Split of split_term * split_kind * split_monitor
  | Merge of split_term
  | Update_dynamic_splits

exception InvalidAction

(* --- Flows --- *)

module MakeFlow (Abstract: Abstractions.Eva) =
struct
  type state = Abstract.Dom.t
  type t =  (key * state) list

  let empty = []

  let initial (p : 'a list) : t =
    List.map (fun state -> Key.empty, state) p

  let to_list (f : t) : state list =
    List.map snd f

  let of_partition (p : state partition) : t =
    KMap.fold (fun k x l -> (k,x) :: l) p []

  let to_partition (p : t) : state partition =
    let add p (k,x) =
      (* Join states with the same key *)
      let x' =
        try
          Abstract.Dom.join (KMap.find k p) x
        with Not_found -> x
      in
      KMap.add k x' p
    in
    List.fold_left add KMap.empty p

  let is_empty (p : t) =
    p = []

  let size (p : t) =
    List.length p

  let union (p1 : t) (p2 : t) : t =
    p1 @ p2

  (* --- Automatic loop unrolling ------------------------------------------- *)

  module AutoLoopUnroll = Auto_loop_unroll.Make (Abstract)

  (* --- Evaluation and split functions ------------------------------------- *)

  (* Evaluation with no reduction and no subdivision. *)
  let evaluate = Abstract.Eval.evaluate ~reduction:false ~subdivnb:0

  exception Operation_failed

  let fail ~exp message =
    let source = fst exp.Cil_types.eloc in
    let warn_and_raise message =
      Self.warning ~source ~once:true "%s" message;
      raise Operation_failed
    in
    Pretty_utils.ksfprintf warn_and_raise message

  let evaluate_exp_to_ival state exp =
    (* Evaluate the expression *)
    let valuation, value =
      match evaluate state exp with
      | `Value (valuation, value), alarms when Alarmset.is_empty alarms ->
        valuation, value
      | _ ->
        fail ~exp "this partitioning parameter cannot be evaluated safely on \
                   all states"
    in
    (* Get the cvalue *)
    let cvalue = match Abstract.Val.get Main_values.CVal.key with
      | Some get_cvalue -> get_cvalue value
      | None -> fail ~exp "partitioning is disabled when the CValue domain is \
                           not active"
    in
    (* Extract the ival *)
    let ival =
      try
        Cvalue.V.project_ival cvalue
      with Cvalue.V.Not_based_on_null ->
        fail ~exp "this partitioning parameter must evaluate to an integer"
    in
    valuation, ival

  exception Split_limit of Integer.t option

  let split_by_value ~monitor state exp =
    let module SplitValues = Datatype.Integer.Set in
    let valuation, ival = evaluate_exp_to_ival state exp in
    (* Build a state with the lvalue set to a singleton *)
    let build i acc =
      let value = Abstract.Val.inject_int (Cil.typeOf exp) i in
      let state =
        let* valuation = Abstract.Eval.assume ~valuation state exp value in
        (* Check the reduction *)
        Abstract.Dom.update (Abstract.Eval.to_domain_valuation valuation) state
      in
      match state with
      | `Value state ->
        let _,new_ival = evaluate_exp_to_ival state exp in
        if not (Ival.is_singleton_int new_ival) then
          fail ~exp "failing to learn perfectly from split" ;
        monitor.split_values <-
          SplitValues.add i monitor.split_values;
        (i, state) :: acc
      | `Bottom -> (* This value cannot be set in the state ; the evaluation of
                      expr was unprecise *)
        acc
    in
    try
      (* Check the size of the ival *)
      begin match Ival.cardinal ival with
        | None -> raise (Split_limit None)
        | Some c as count ->
          if Integer.(gt c (of_int monitor.split_limit)) then
            raise (Split_limit count)
      end;
      (* For each integer of the ival, build a new state *)
      try
        let result = Ival.fold_int build ival [] in
        let c = SplitValues.cardinal monitor.split_values in
        if c > monitor.split_limit then
          raise (Split_limit (Some (Integer.of_int c)));
        result
      with Abstract_interp.Error_Top -> (* The ival is float *)
        raise (Split_limit None)
    with
    | Split_limit count ->
      let pp_count fmt =
        match count with
        | None -> ()
        | Some c -> Format.fprintf fmt " (%a)" Integer.pretty c
      in
      fail ~exp "split on more than %d values%t prevented ; try to improve \
                 the analysis precision or look at the option -eva-split-limit \
                 to increase this limit."
        monitor.split_limit pp_count

  let eval_exp_to_int state exp =
    let _valuation, ival = evaluate_exp_to_ival state exp in
    try Integer.to_int_exn (Ival.project_int ival)
    with
    | Ival.Not_Singleton_Int ->
      fail ~exp "this partitioning parameter must evaluate to a singleton"
    | Z.Overflow -> fail ~exp "this partitioning parameter overflows an integer"

  let split_by_predicate state predicate =
    let env =
      let states = function _ -> Abstract.Dom.top in
      Abstract_domain.{ states; result = None }
    in
    let source = fst (predicate.Cil_types.pred_loc) in
    let aux positive =
      let+ state' =
        Abstract.Dom.reduce_by_predicate env state predicate positive in
      let x = Abstract.Dom.evaluate_predicate env state' predicate in
      if x == Unknown
      then
        Self.warning ~source ~once:true
          "failing to learn perfectly from split predicate";
      if Abstract.Dom.equal state' state then raise Operation_failed;
      let value = if positive then Integer.one else Integer.zero in
      value, state'
    in
    Bottom.list_values [ aux true; aux false ]

  (* --- Applying partitioning actions onto flows --------------------------- *)

  let stamp_by_value = match Abstract.Val.get Main_values.CVal.key with
    | None -> fun _ _ _ -> None
    | Some get -> fun expr expected_values state ->
      let typ = Cil.typeOf expr in
      let make stamp i = stamp, i, Abstract.Val.inject_int typ i in
      let expected_values = List.mapi make expected_values in
      match fst (evaluate state expr) with
      | `Bottom -> None
      | `Value (_cache, value) ->
        let is_included (_, _, v) = Abstract.Val.is_included v value in
        match List.find_opt is_included expected_values with
        | None -> None
        | Some (stamp, i, _) ->
          if Cvalue.V.cardinal_zero_or_one (get value)
          then Some (stamp, 0)
          else begin
            Self.result ~once:true ~current:true
              "cannot properly split on \\result == %a"
              Abstract_interp.Int.pretty i;
            None
          end

  let split_state ~monitor term (key, state) : (key * state) list =
    try
      let update_key (v, x) =
        { key with splits = SplitMap.add term v key.splits }, x
      in
      let states =
        match term with
        | Expression exp -> split_by_value ~monitor state exp
        | Predicate pred -> split_by_predicate state pred
      in
      List.map update_key states
    with Operation_failed -> [(key,state)]

  let split ~monitor (kind : split_kind) (term : split_term) (p : t) =
    let add_split (key, state) =
      let dynamic_splits =
        match kind with
        | Static -> SplitMap.remove term key.dynamic_splits
        | Dynamic -> SplitMap.add term monitor key.dynamic_splits
      in
      let key = { key with dynamic_splits } in
      split_state ~monitor term (key, state)
    in
    Transitioning.List.concat_map add_split p

  let update_dynamic_splits p =
    (* Update one state *)
    let update_state (key, state) =
      (* Split the states in the list l for the given exp *)
      let update_exp term monitor l =
        Transitioning.List.concat_map (split_state ~monitor term) l
      in
      (* Foreach exp in original state: split *)
      SplitMap.fold update_exp key.dynamic_splits [(key,state)]
    in
    Transitioning.List.concat_map update_state p

  let map_keys (f : key -> state -> key) (p : t) : t =
    List.map (fun (k,x) -> f k x, x) p

  let transfer_keys p = function
    | Split (expr, kind, monitor) ->
      split ~monitor kind expr p

    | Update_dynamic_splits ->
      update_dynamic_splits p

    | action -> (* Simple map transfer functions *)
      let transfer = match action with
        | Split _ | Update_dynamic_splits ->
          assert false (* Handled above *)

        | Enter_loop limit_kind -> fun k x ->
          let limit = try match limit_kind with
            | ExpLimit exp -> eval_exp_to_int x exp
            | IntLimit i -> i
            | AutoUnroll (stmt, min_unroll, max_unroll) ->
              match AutoLoopUnroll.compute ~max_unroll x stmt with
              | None -> min_unroll
              | Some i ->
                let source = fst (Cil_datatype.Stmt.loc stmt) in
                Self.warning ~once:true ~current:true ~source
                  ~wkey:Self.wkey_loop_unroll_auto
                  "Automatic loop unrolling.";
                i
            with
            | Operation_failed -> 0
          in
          { k with loops = (0,limit) :: k.loops }

        | Leave_loop -> fun k _x ->
          begin match k.loops with
            | [] -> raise InvalidAction
            | _ :: tl -> { k with loops = tl }
          end

        | Incr_loop -> fun k _x ->
          begin match k.loops with
            | [] -> raise InvalidAction
            | (h, limit) :: tl ->
              if h >= limit then begin
                if limit > 0 then
                  Self.warning ~once:true ~current:true
                    ~wkey:Self.wkey_loop_unroll_partial
                    "loop not completely unrolled";
                k
              end
              else
                { k with loops = (h + 1, limit) :: tl }
          end

        | Branch (b,max) -> fun k _x ->
          if max > 0 then
            { k with branches = b :: Extlib.list_first_n (max - 1) k.branches  }
          else if k.branches <> [] then
            { k with branches = [] }
          else
            k

        | Ration { current; limit; merge } ->
          let length = List.length p in
          (* The incoming states exceed the rationing limit: no more stamps. *)
          if !current + length > limit then begin
            current := limit;
            fun k _ -> { k with ration_stamp = None }
          end
          (* If merge, a unique ration stamp for all incoming states. *)
          else if merge then begin
            current := !current + length;
            fun k _ -> { k with ration_stamp = Some (!current, 0) }
          end
          (* Default case: a different stamp for each incoming state. *)
          else
            let stamp () = incr current; Some (!current, 0) in
            fun k _ -> { k with ration_stamp = stamp () }

        | Restrict (expr, expected_values) -> fun k s ->
          { k with ration_stamp = stamp_by_value expr expected_values s}

        | Merge term -> fun k _x ->
          { k with splits = SplitMap.remove term k.splits;
                   dynamic_splits = SplitMap.remove term k.dynamic_splits }
      in
      map_keys transfer p

  let transfer (f : (key * state) -> (key * state) list) (p : t) : t =
    let n = ref 0 in
    let transfer acc key_state =
      let add l (k, y) =
        match k.ration_stamp with
        (* No ration stamp, just add the state to the list *)
        | None -> (k, y) :: l
        (* There is a ration stamp, set the second part of the stamp to a unique transfer number *)
        | Some (s,_) ->
          let k' = { k with ration_stamp = Some (s, !n) } in
          incr n;
          (k', y) :: l
      in
      List.fold_left add acc (f key_state)
    in
    List.fold_left transfer [] p

  let iter (f : state -> unit) (p : t) : unit =
    List.iter (fun (_k,x) -> f x) p

  let join_duplicate_keys (p : t) : t =
    let cmp (k, _) (k', _) = Key.compare k k' in
    let p = List.fast_sort cmp p in
    let rec aux acc (key, state) = function
      | [] -> (key, state) :: acc
      | (key', state') :: tl ->
        if Key.compare key key' = 0
        then aux acc (key, Abstract.Dom.join state state') tl
        else aux ((key, state) :: acc) (key', state') tl
    in
    match p with
    | [] | [_] -> p
    | e :: tl -> aux [] e tl

  let filter_map (f: key -> state -> state option) (p : t) : t =
    let rec aux = function
      | [] -> []
      | (key, x) :: tl -> match f key x with
        | Some y -> (key, y) :: (aux tl)
        | None -> aux tl
    in
    aux p
end
