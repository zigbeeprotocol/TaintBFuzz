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
open Lattice_bounds

let dkey = Self.register_category "d-multidim"

let map_to_singleton map =
  let aux base offset = function
    | None -> Some (base, offset)
    | Some _ -> raise Exit
  in
  try Base.Base.Map.fold aux map None with Exit -> None

module Value =
struct
  include Cvalue.V
  include Cvalue_forward (* for fallback oracles *)

  let backward_is_finite positive fkind v =
    let prec = Fval.kind fkind in
    try
      let v = reinterpret_as_float fkind v in
      Fval.backward_is_finite ~positive prec (project_float v) >>-: inject_float
    with Not_based_on_null ->
      `Value v
end

module Value_or_Uninitialized =
struct
  open Cvalue
  include V_Or_Uninitialized

  let to_integer cvalue =
    try  Some (Ival.project_int (V.project_ival (get_v cvalue)))
    with V.Not_based_on_null | Ival.Not_Singleton_Int -> None

  let get_v_normalized x =
    let v' = get_v x in
    if V.is_bottom v'
    then `Bottom
    else `Value v'

  let make i v =
    let initialized = match i with
      | Abstract_memory.SurelyInitialized -> true
      | Abstract_memory.MaybeUninitialized -> false
    in
    V_Or_Uninitialized.make ~initialized ~escaping:false v

  let of_value v =
    V_Or_Uninitialized.make ~initialized:true ~escaping:false v

  let of_bit ~typ:_ = function
    | Abstract_memory.Uninitialized -> uninitialized
    | Zero i -> make i (V.inject_int Integer.zero)
    | Any (Top, i) -> make i (V.top_with_origin Origin.top)
    | Any (Set s, i) ->
      let v =
        if Base.Hptset.is_empty s
        then V.inject_ival Ival.top
        else V.inject_top_origin Origin.top s
      in
      make i v

  let to_bit v' =
    match get_v_normalized v' with
    | `Bottom -> Abstract_memory.Uninitialized
    | `Value v ->
      let initialization =
        if is_initialized v'
        then Abstract_memory.SurelyInitialized
        else Abstract_memory.MaybeUninitialized
      in
      if V.is_zero v
      then Abstract_memory.Zero (initialization)
      else Abstract_memory.Any (V.get_bases v, initialization)

  let from_flagged fv =
    V_Or_Uninitialized.make
      ~initialized:fv.initialized
      ~escaping:false
      (Bottom.value ~bottom:V.bottom fv.v)

  let map' f v =
    let+ new_v = f (get_v v) in
    map (fun _ -> new_v) v
end

let convert_oracle oracle =
  fun exp ->
  match Ival.project_int_val (Value.project_ival (oracle exp)) with
  | Some int_val -> int_val
  | None | exception Value.Not_based_on_null -> Int_val.top

type assigned = (Precise_locs.precise_location,Value.t) Eval.assigned
type builtin = assigned list -> assigned or_bottom

let builtins : (string * builtin) list = []

let find_builtin =
  let module Table = Stdlib.Hashtbl in
  let table = Table.create 17 in
  List.iter (fun (name, f) -> Table.replace table name f) builtins;
  fun kf ->
    try Some (Table.find table (Kernel_function.get_name kf))
    with Not_found -> None


module Location =
struct
  module Offset = Abstract_offset
  module Map = Base.Base.Map
  open Top.Operators

  type offset = Offset.t or_top
  type base = Base.t
  type t = offset Map.t

  let _pretty =
    Pretty_utils.pp_iter2 ~sep:",@," ~between:":"
      Map.iter Base.pretty Offset.pretty

  let empty = Map.empty

  let fold : (base-> offset -> 'a -> 'a) -> t -> 'a -> 'a = Map.fold

  let bases map =
    Map.fold (fun b _ acc -> b :: acc) map []

  let is_singleton map =
    match map_to_singleton map with
    | None -> false
    | Some (b,o) ->
      match o with
      | `Top -> false
      | `Value o -> not (Base.is_weak b) && Offset.is_singleton o

  let to_singleton_var map =
    match map_to_singleton map with
    | Some (Base.Var (vi, _), `Value (Offset.NoOffset t)) (* maybe too restrictive *)
      when Typed_memory.are_typ_compatible vi.vtype t -> Some (vi)
    | _ -> None

  let references (map : t) =
    let module Set = Cil_datatype.Varinfo.Set in
    let add_refs _b o acc =
      match o with
      | `Top -> acc
      | `Value o -> Set.union (Offset.references o) acc
    in
    Map.fold add_refs map Set.empty |> Set.elements

  let of_var (vi : Cil_types.varinfo) : t =
    Map.singleton (Base.of_varinfo vi) (`Value (Offset.of_var_address vi))

  let of_lval oracle ((host,offset) as lval : Cil_types.lval) : t or_top =
    let oracle' = convert_oracle oracle in
    let base_typ = Cil.typeOfLhost host in
    let offset =
      if Cil.typeHasQualifier "volatile" (Cil.typeOfLval lval) then
        `Top
      else
        Offset.of_cil_offset oracle' base_typ offset in
    match host with
    | Var vi ->
      `Value (Map.singleton (Base.of_varinfo vi) offset)
    | Mem exp ->
      let exp, index = match exp.enode with
        | BinOp (PlusPI, e1, e2, _typ) ->
          e1, Some e2
        | _ -> exp, None
      in
      let add base ival map =
        let offset' : Offset.t or_top =
          match Base.typeof base with
          | None -> `Top
          | Some base_typ ->
            let typ = Cil.typeOf_pointed (Cil.typeOf exp) in
            let* base_offset = Offset.of_ival ~base_typ ~typ ival in
            let* base_offset = match index with
              | None -> `Value (base_offset)
              | Some exp ->
                Offset.add_index oracle' base_offset exp
            in
            let+ offset = offset in
            Offset.append base_offset offset
        in
        Map.add base offset' map
      in
      let loc = Locations.loc_bytes_to_loc_bits (oracle exp) in
      try
        `Value (Locations.Location_Bits.fold_topset_ok add loc Map.empty)
      with Abstract_interp.Error_Top ->
        `Top

  let of_term_lval env ((lhost, offset) as lval) =
    let+ vi = match lhost with
      | TVar ({lv_origin=Some vi}) -> `Value (vi)
      | TResult _ -> Top.of_option env.Abstract_domain.result
      | _ -> `Top
    in
    let base' = Base.of_varinfo vi in
    let offset' = Offset.of_term_offset vi.vtype offset in
    Map.singleton base' offset', Cil.typeOfTermLval lval

  let of_term env t =
    match t.term_node with
    | TLval term_lval -> of_term_lval env term_lval
    | _ -> `Top

  let of_precise_loc loc =
    let loc' = Precise_locs.imprecise_location loc in
    let add_base base map =
      (* Null base doesn't have a type ; use void instead *)
      let typ = Option.value ~default:Cil.voidType (Base.typeof base) in
      Map.add base (`Value (Offset.NoOffset typ)) map
    in
    Locations.Location_Bits.(fold_bases add_base loc'.loc empty)
end


(* Redefines the memory domain so it can handle top locations *)

module Memory =
struct
  module Config = struct
    let deps = [Ast.self]
    let slice_limit = Parameters.MultidimSegmentLimit.get
    let disjunctive_invariants =
      Parameters.MultidimDisjunctiveInvariants.get
  end
  module Memory = Typed_memory.Make (Config) (Value_or_Uninitialized)

  module Prototype =
  (* Datatype *)
  struct
    include Datatype.Undefined
    include Memory
    let name = "Multidim_domain.Memory"
    let reprs = [ Memory.top ]
  end

  include Datatype.Make (Prototype)

  let pretty = Memory.pretty
  let _pretty_debug = Memory.pretty
  let top = Memory.top
  let is_top = Memory.is_top
  let is_included = Memory.is_included
  let narrow = fun m1 _m2 -> m1
  let join = Memory.join
  let smash ~oracle = Memory.join ~oracle:(fun _ -> oracle)
  let widen h =
    Memory.widen
      (fun ~size v1 v2 -> Value_or_Uninitialized.widen (size,h) v1 v2)
  let incr_bound = Memory.incr_bound

  let get ~oracle m loc =
    match loc with
    | `Top -> Value_or_Uninitialized.top
    | `Value loc -> Memory.get ~oracle m loc

  let extract ~oracle m loc =
    match loc with
    | `Top -> Memory.top
    | `Value loc -> Memory.extract ~oracle m loc

  let erase ~oracle ~weak m loc bit_value =
    match loc with
    | `Top -> Memory.top
    | `Value loc -> Memory.erase ~oracle ~weak m loc bit_value

  let set ~oracle ~weak new_v m loc =
    match loc with
    | `Top -> Memory.top
    | `Value loc ->
      Memory.set ~oracle ~weak m loc new_v

  let reinforce ~oracle f m loc =
    match loc with
    | `Top -> `Value m
    | `Value loc ->
      Memory.reinforce ~oracle f m loc

  let overwrite ~oracle ~weak dst loc src =
    match loc with
    | `Top -> Memory.top
    | `Value loc ->
      Memory.overwrite ~oracle ~weak dst loc src

  let segmentation_hint ~oracle m loc bounds =
    match loc with
    | `Top -> Memory.top
    | `Value loc ->
      Memory.segmentation_hint ~oracle m loc bounds
end

module DomainLattice =
struct
  open Bottom.Operators
  (* References to variables inside array segmentation.
     For instance if an array A is described with the segmentation
      0..i-1 ; i ; i+1..10
     then, everytime i is changed, the segmentation must be updated. This requires
     referencing every base where at least one segmentation references i. *)
  module Referers = Base.Hptset (* The set of bases referencing the variable *)
  (* The domain can be set to track a subset of bases *)
  module Tracking = Base.Hptset

  (* The domain is essentially a map from bases to individual memory abstractions *)
  module Initial_Values = struct let v = [[]] end
  module Deps = struct let l = [Ast.self] end
  module V =
  struct
    include Datatype.Pair (Memory) (Referers)
    let pretty_debug = pretty
    let top = Memory.top, Referers.empty
    let is_top (m,r) = Memory.is_top m && Referers.is_empty r
  end

  module BaseMap =
  struct
    include
      Hptmap.Make
        (Base.Base) (V)
        (Hptmap.Comp_unused) (Initial_Values) (Deps)

    let find_or_top (state : t) (b : Base.t) =
      try find b state with Not_found -> V.top

    (* Update or remove if top *)
    let add (b : Base.t) (v : V.t) (state : t) =
      if V.is_top v
      then remove b state
      else add b v state

  end

  include Datatype.Pair_with_collections
      (BaseMap)
      (Datatype.Option (Tracking))
      (struct let module_name = "DomainLattice" end)

  type state = t
  type value = Value.t
  type value_or_uninitialized = Value_or_Uninitialized.t
  type base = Base.t
  type offset = Location.offset
  type memory = Memory.t
  type location = Precise_locs.precise_location
  type mdlocation = Location.t (* should be = to location *)
  type origin

  let log_category = dkey

  let cache_name s =
    Hptmap_sig.PersistentCache ("Multidim_domain." ^ s)

  (* Bases handling *)

  let covers_base (tracked : Tracking.t option) (b : base) : bool =
    match b with
    | Base.Var (vi, _) ->
      not (Cil.typeHasQualifier "volatile" vi.vtype) &&
      Option.fold ~none:true ~some:(Tracking.mem b) tracked
    | Null -> true
    | CLogic_Var _ | String _ | Allocated (_, _, _) -> false

  let join_tracked tracked1 tracked2 =
    match tracked1, tracked2 with
    | None, tracked | tracked, None -> tracked
    | Some s1, Some s2 -> Some (Tracking.union s1 s2)


  (* References *)

  let add_references (state : t) (referee : base) (referers' : base list) : t =
    let base_map, tracked = state in
    let memory, referers = BaseMap.find_or_top base_map referee in
    let referers'' = Referers.union referers (Referers.of_list referers') in
    BaseMap.add referee (memory, referers'') base_map, tracked

  let add_references_l state (referees : base list) (referers : base list) =
    List.fold_left
      (fun state b -> add_references state b referers)
      state referees

  let update_var_references ~oracle (dst : Cil_types.varinfo)
      (src : Cil_types.exp option) (base_map,tracked : t) =
    let incr = Option.bind src (fun expr ->
        match expr.Cil_types.enode with
        | BinOp ((PlusA|PlusPI), { enode=Lval (Var vi', NoOffset) }, exp, _typ)
          when Cil_datatype.Varinfo.equal dst vi' ->
          Cil.constFoldToInt exp
        | BinOp ((PlusA|PlusPI), exp, { enode=Lval (Var vi', NoOffset)}, _typ)
          when Cil_datatype.Varinfo.equal dst vi' ->
          Cil.constFoldToInt exp
        | BinOp ((MinusA|MinusPI), { enode=Lval (Var vi', NoOffset) }, exp, _typ)
          when Cil_datatype.Varinfo.equal dst vi' ->
          Option.map Integer.neg (Cil.constFoldToInt exp)
        | _ -> None)
    in
    (* [oracle] must be the oracle before the (non-invertible)
       assignement of the referee to allow removing of eventual empty slice
       before the bound leaves the segmentation. *)
    let referers = snd (BaseMap.find_or_top base_map (Base.of_varinfo dst)) in
    let update_ref base base_map =
      let update (memory, refs) =
        let oracle = convert_oracle oracle in
        Memory.incr_bound ~oracle dst incr memory, refs
      in
      BaseMap.replace (Option.map update) base base_map
    in
    let base_map = Referers.fold update_ref referers base_map in
    (* If increment is None, every reference to dst should have been removed by
        Memory.incr_bound *)
    let base_map =
      if Option.is_none incr then
        BaseMap.replace
          (Option.map (fun (memory, _refs) -> memory, Referers.empty))
          (Base.of_varinfo dst)
          base_map
      else
        base_map
    in
    base_map, tracked

  let update_references ~oracle (dst : mdlocation)
      (src : Cil_types.exp option) (state : t) =
    let remove_references b state =
      match Base.to_varinfo b with
      | exception Base.Not_a_C_variable -> state (* only references to variables are kept *)
      | vi -> update_var_references ~oracle vi None state
    in
    match Location.to_singleton_var dst with
    | Some vi ->
      update_var_references ~oracle vi src state
    | None -> (* Weak update of referee, remove references *)
      Location.fold (fun b _offset state -> remove_references b state) dst state


  (* Accesses *)

  let read :
    type a .
    (memory -> offset -> a) -> (a -> a -> a) ->
    state -> mdlocation -> a or_bottom =
    fun map reduce (state,_tracked) loc ->
    let f base off acc =
      let v = map (fst (BaseMap.find_or_top state base)) off in
      Bottom.join reduce (`Value v) acc
    in
    Location.fold f loc `Bottom

  let get ~oracle
      (state : state) (src : mdlocation) : value_or_uninitialized or_bottom =
    let oracle = convert_oracle oracle in
    read (Memory.get ~oracle) Value_or_Uninitialized.join state src

  let mk_oracle (state : state) : Cil_types.exp -> value =
    (* Until Eva gives access to good oracles, we use this poor stupid oracle
       instead *)
    let rec oracle exp =
      match exp.enode with
      | Lval lval ->
        begin match Location.of_lval oracle lval with
          | `Top -> Value.top
          | `Value loc ->
            match get ~oracle state loc with
            | `Bottom -> Value.bottom (* should never happen as location should not be empty *)
            | `Value v -> Value_or_Uninitialized.get_v v
        end
      | Const (CInt64 (i,_,_)) ->
        Value.inject_int i
      | Const (CReal (f,_,_)) ->
        Value.inject_float (Fval.singleton (Fval.F.of_float f))
      | UnOp (op, e, typ) ->
        Value.forward_unop typ op (oracle e)
      | BinOp (op, e1, e2, TFloat (fkind, _)) ->
        Value.forward_binop_float (Fval.kind fkind) (oracle e1) op (oracle e2)
      | BinOp (op, e1, e2, typ) ->
        Value.forward_binop_int ~typ (oracle e1) op (oracle e2)
      | CastE (typ, e) ->
        let scalar_type t = Option.get (Eval_typ.classify_as_scalar t) in
        let src_type =  scalar_type (Cil.typeOf e)
        and dst_type = scalar_type typ in
        Value.forward_cast ~src_type ~dst_type (oracle e)
      | _ ->
        Self.fatal
          "This type of array index expression is not supported: %a"
          Cil_printer.pp_exp exp
    in
    fun exp -> oracle (Cil.constFold true exp)

  let mk_bioracle s1 s2 =
    let oracle_left = mk_oracle s1
    and oracle_right = mk_oracle s2 in
    function
    | Abstract_memory.Left -> convert_oracle oracle_left
    | Right -> convert_oracle oracle_right

  let extract ~oracle (state : state) (src : mdlocation) : Memory.t or_bottom =
    let oracle = convert_oracle oracle in
    read (Memory.extract ~oracle) (Memory.smash ~oracle) state src

  let write' (update : memory -> offset -> memory or_bottom)
      (state : state) (loc : mdlocation) : state or_bottom =
    let deps = List.map Base.of_varinfo (Location.references loc) in
    let deps_set = Tracking.of_list deps in
    let f base off state' =
      let* base_map,tracked = state' in
      if covers_base tracked base then
        let memory, refs = BaseMap.find_or_top base_map base in
        let+ memory' = update memory off in
        BaseMap.add base (memory', refs) base_map,
        Option.map (Tracking.union deps_set) tracked
      else
        state'
    in
    let+ state = Location.fold f loc (`Value state) in
    add_references_l state deps (Location.bases loc)

  let write update state loc =
    (* Result can never be bottom if update never returns bottom *)
    Bottom.non_bottom (write' (fun m o -> `Value (update m o)) state loc)

  let set ~oracle
      (state : state) (dst : mdlocation) (v : value_or_uninitialized) : state =
    let weak = not (Location.is_singleton dst)
    and oracle = convert_oracle oracle in
    write (Memory.set ~oracle ~weak v) state dst

  let overwrite ~oracle
      (state : state) (dst : mdlocation) (src : mdlocation) : state =
    let weak = not (Location.is_singleton dst) in
    match extract ~oracle state src with
    | `Bottom -> state (* no source *)
    | `Value value ->
      let oracle = convert_oracle oracle in
      write (fun m off -> Memory.overwrite ~oracle ~weak m off value) state dst

  let erase ~oracle ?(weak: bool option)
      (state : state) (dst : mdlocation) (b : Abstract_memory.bit) : state =
    let oracle = convert_oracle oracle
    and weak = match weak with
      | None -> not (Location.is_singleton dst)
      | Some weak -> weak
    in
    write (fun m off -> Memory.erase ~oracle ~weak m off b) state dst

  let reinforce
      ~oracle
      (f : value_or_uninitialized -> value_or_uninitialized or_bottom)
      (state : state) (dst : mdlocation) : state or_bottom =
    let oracle = convert_oracle oracle in
    write' (fun m off -> Memory.reinforce ~oracle f m off) state dst

  let remove ~oracle (vi : Cil_types.varinfo) (state : t) =
    let state = update_var_references ~oracle vi None state in
    let map, tracked = state in
    BaseMap.remove (Base.of_varinfo vi) map, tracked


  (* Lattice *)

  let top = BaseMap.empty, None

  let is_included =
    let open BaseMap in
    let cache = cache_name "is_included" in
    let decide_fst _b _v1 = true (* v2 is top *) in
    let decide_snd _b _v2 = false (* v1 is top, v2 is not *) in
    let decide_both _ (m1,_r1) (m2,_r2) = Memory.is_included m1 m2 in
    let decide_fast s t = if s == t then PTrue else PUnknown in
    let is_included = binary_predicate cache UniversalPredicate
        ~decide_fast ~decide_fst ~decide_snd ~decide_both
    in
    fun (m1,_) (m2,_) -> is_included m1 m2

  let narrow =
    let open BaseMap in
    let cache = cache_name "narrow" in
    let decide _ v1 v2 = Memory.narrow v1 v2 in
    let narrow = join ~cache ~symmetric:false ~idempotent:true ~decide in
    fun (m1,t1) (m2,t2) -> `Value (narrow m1 m2, join_tracked t1 t2)

  let join' ~oracle (m1,t1) (m2,t2) =
    let open BaseMap in
    let cache = Hptmap_sig.NoCache
    and decide _ x1 x2 =
      let m1,r1 = Option.value ~default:V.top x1
      and m2,r2 = Option.value ~default:V.top x2 in
      Memory.join ~oracle m1 m2, Referers.union r1 r2 (* TODO: Remove tops *)
    in
    generic_join ~cache ~symmetric:false ~idempotent:true ~decide m1 m2,
    join_tracked t1 t2

  let join s1 s2 =
    let oracle = mk_bioracle s1 s2 in
    join' ~oracle s1 s2

  let widen kf stmt (m1,t1 as s1) (m2,t2 as s2) =
    let open BaseMap in
    let oracle = mk_bioracle s1 s2
    and _,get_hints = Widen.getWidenHints kf stmt in
    let cache = Hptmap_sig.NoCache
    and decide base x1 x2 =
      let m1,r1 = Option.value ~default:V.top x1
      and m2,r2 = Option.value ~default:V.top x2 in
      Memory.widen ~oracle (get_hints base) m1 m2, Referers.union r1 r2
    in
    generic_join ~cache ~symmetric:false ~idempotent:true ~decide m1 m2,
    join_tracked t1 t2
end

module Domain =
struct
  include DomainLattice
  include Domain_builder.Complete (DomainLattice)

  (* Eva Queries *)

  (* Nothing interesting to be done on expressions *)
  let extract_expr ~oracle:_ _context _state _expr =
    `Value (Value.top, None), Alarmset.all

  let extract_lval ~oracle _context state lv typ _loc =
    if Cil.isScalarType typ then
      let oracle = fun exp ->
        match oracle exp with
        | `Value v, alarms when Alarmset.is_empty alarms -> v (* only use values safely evaluated *)
        | _ -> Value.top
      in
      match Location.of_lval oracle lv with
      | `Top -> (* can't evaluate location *)
        `Value (Value.top, None), Alarmset.all
      | `Value loc ->
        match get ~oracle state loc with
        | `Bottom -> `Bottom, Alarmset.all
        | `Value v ->
          Value_or_Uninitialized.get_v_normalized v >>-: (fun v -> v, None),
          if Value_or_Uninitialized.is_initialized v
          then Alarmset.(set (Alarms.Uninitialized lv) True all)
          else Alarmset.all
    else
      `Value (Value.top, None), Alarmset.all


  (* Eva Transfer *)

  let valuation_to_oracle state valuation : Cil_types.exp -> value = fun exp ->
    let multidim_oracle = mk_oracle state in
    match valuation.Abstract_domain.find exp with
    | `Top -> multidim_oracle exp
    | `Value {value={v=`Bottom}} -> Value.bottom
    | `Value {value={v=`Value value}} -> value

  let assume_exp valuation expr record state' =
    let* state = state' in
    let oracle = valuation_to_oracle state valuation in
    match expr.enode with
    | Lval lv when Cil.isScalarType (Cil.typeOfLval lv) ->
      let value = Value_or_Uninitialized.from_flagged record.value in
      if not (Value.is_topint (Value_or_Uninitialized.get_v value)) then
        match Location.of_lval oracle lv with
        | `Top -> `Value state (* location evaluate to top, ignore *)
        | `Value loc ->
          let update value' =
            let v = Value_or_Uninitialized.narrow value value' in
            (* The value can legitimately be bottom on escaping variables,
               which are not tracked by the multidim domain.
               In this case, do not reduce the state to bottom. *)
            if Value_or_Uninitialized.is_bottom v && not record.value.escaping
            then `Bottom
            else `Value v
          in
          if Location.is_singleton loc
          then reinforce ~oracle update state loc
          else `Value state
      else `Value state
    | _ -> `Value state

  let assume_valuation valuation state =
    valuation.Abstract_domain.fold (assume_exp valuation) (`Value state)

  let update valuation state =
    assume_valuation valuation state

  let assign' ~oracle ~value dst src state =
    match Location.of_lval oracle dst with
    | `Top -> top
    | `Value dst ->
      let state = update_references ~oracle dst src state in
      match value with
      | Assign value ->
        set ~oracle state dst (Value_or_Uninitialized.of_value value)
      | Copy (right, value) ->
        match Location.of_lval oracle right.lval with
        | `Top ->
          let b = Value_or_Uninitialized.(to_bit (from_flagged value)) in
          erase ~oracle state dst b
        | `Value src ->
          overwrite ~oracle state dst src

  let assign _kinstr { lval=dst; ltyp } src assigned_value valuation state =
    if Int_Base.is_zero (Bit_utils.sizeof ltyp)
    then `Value state
    else
      let+ state = assume_valuation valuation state in
      let oracle = valuation_to_oracle state valuation in
      assign' ~oracle ~value:assigned_value dst (Some src) state

  let assume _stmt _expr _pos valuation state =
    assume_valuation valuation state

  let start_call _stmt call recursion valuation state =
    if recursion <> None
    then
      Self.abort ~current:true
        "The multidim domain does not support recursive calls yet";
    let oracle = valuation_to_oracle state valuation in
    let bind state arg =
      state >>-:
      assign' ~oracle ~value:arg.avalue (Cil.var arg.formal) (Some arg.concrete)
    in
    List.fold_left bind (`Value state) call.arguments

  let finalize_call _stmt call _recursion ~pre:_ ~post =
    match find_builtin call.kf, call.return with
    | None, _ | _, None   -> `Value post
    | Some f, Some return ->
      let args = List.map (fun arg -> arg.avalue) call.arguments in
      let+ assigned_result = f args in
      let oracle = mk_oracle post in
      assign' ~oracle ~value:assigned_result (Cil.var return) None post

  let show_expr valuation state fmt expr =
    match expr.enode with
    | Lval lval | StartOf lval ->
      let oracle = valuation_to_oracle state valuation in
      begin match Location.of_lval oracle lval with
        | `Top -> Format.fprintf fmt "%s" (Unicode.top_string ())
        | `Value loc ->
          let m = extract ~oracle state loc in
          Bottom.pretty Memory.pretty fmt m
      end
    | _ -> ()

  let enter_scope _kind vars state =
    let oracle = mk_oracle state in
    let enter_one state v =
      let dst = Location.of_var v in
      erase ~oracle state dst Abstract_memory.Bit.uninitialized
    in
    List.fold_left enter_one state vars

  let leave_scope _kf vars state =
    let oracle = mk_oracle state in
    List.fold_left (fun state vi -> remove ~oracle vi state) state vars

  let logic_assign assign location state =
    let oracle = mk_oracle state
    and dst = Location.of_precise_loc location
    and b =
      match assign with
      | None
      | Some (Frees _, _)
      | Some (Allocates _, _)
      | Some (Assigns (_, _ :: _), _) -> Abstract_memory.Bit.top
      | Some (Assigns (_, []), _) -> Abstract_memory.Bit.numerical
    in
    let state = update_references ~oracle dst None state in
    erase ~oracle ~weak:true state dst b

  let reduce_by_papp env li _labels args positive state =
    match li.l_var_info.lv_name, args with
    | "\\are_finite", [arg] ->
      begin match Location.of_term env arg with
        | `Top -> `Value state (* can't resolve location, ignore *)
        | `Value (loc,typ) ->
          begin match Cil.unrollType (Logic_utils.logicCType typ) with
            | TFloat (fkind,_) ->
              let update = Value.backward_is_finite positive fkind
              and oracle = mk_oracle state in
              reinforce ~oracle (Value_or_Uninitialized.map' update) state loc
            | _ | exception (Failure _) -> `Value state
          end
      end
    | _ -> `Value state

  let reduce_by_predicate env state predicate truth =
    let rec reduce predicate truth state =
      match truth, predicate.pred_content with
      | true, Pand (p1,p2) | false, Por (p1,p2) ->
        state |> reduce p1 truth >>- reduce p2 truth
      | _,Papp (li, labels, args) ->
        reduce_by_papp env li labels args truth state
      | _ -> `Value state
    in
    reduce predicate truth state

  let interpret_acsl_extension extension _env state =
    match extension.ext_name with
    | "array_partition" ->
      let annotation = Eva_annotations.read_array_segmentation extension in
      let vi,offset,bounds = annotation in
      (* Update the segmentation *)
      let lval = Cil_types.Var vi, offset in
      let oracle = mk_oracle state in
      begin match Location.of_lval oracle lval with
        | `Top -> state
        | `Value loc ->
          let update m offset =
            let oracle = convert_oracle oracle in
            Memory.segmentation_hint ~oracle m offset bounds
          in
          let state = write update state loc in
          (* Update the references *)
          let add acc e =
            let r = Cil.extract_varinfos_from_exp e in
            (Cil_datatype.Varinfo.Set.to_seq r |> List.of_seq) @ acc
          in
          let references = List.fold_left add [] bounds in
          let references = List.map Base.of_varinfo references in
          add_references_l state references (Location.bases loc)
      end
    | "eva_domain_scope" ->
      let domain,vars = Eva_annotations.read_domain_scope extension in
      if domain = "multidim" then
        let (base_map,tracked) = state in
        let set = Option.value ~default:Tracking.empty tracked
        and bases = List.map Base.of_varinfo vars in
        let tracked = List.fold_right Tracking.add bases set in
        let base_map = BaseMap.inter_with_shape tracked base_map in (* Only keep tracked bases in the current base map *)
        base_map, Some tracked
      else
        state
    | _ ->
      state

  let empty () = top

  let initialize_variable lval _loc ~initialized:_ init_value state =
    let oracle = mk_oracle state in
    match Location.of_lval oracle lval with
    | `Top -> top
    | `Value dst ->
      let d = match init_value with
        | Abstract_domain.Top  -> Abstract_memory.Bit.numerical
        | Abstract_domain.Zero -> Abstract_memory.Bit.zero
      in
      let oracle = mk_oracle state in (* Since dst has no offset, oracle is actually useless *)
      erase ~oracle state dst d

  let initialize_variable_using_type _kind vi state =
    let lval = Cil.var vi in
    let oracle = mk_oracle state in
    match Location.of_lval oracle lval with
    | `Top -> top
    | `Value dst ->
      let oracle = mk_oracle state in (* Since dst has no offset, oracle is actually useless *)
      erase ~oracle state dst Abstract_memory.Bit.top

  let relate _kf _bases _state = Base.SetLattice.empty

  let filter _kf _kind bases (base_map,tracked : t) =
    BaseMap.filter (fun elt -> Base.Hptset.mem elt bases) base_map,
    Option.map (Tracking.inter bases) tracked

  let reuse _kf bases =
    let open BaseMap in
    let cache = Hptmap_sig.NoCache in
    let decide_both _key _v1 v2 = Some v2 in
    let decide_left key v1 =
      if Base.Hptset.mem key bases then None else Some v1
    in
    let reuse = merge ~cache ~symmetric:false ~idempotent:true
        ~decide_both ~decide_left:(Traversing decide_left) ~decide_right:Neutral
    in
    fun ~current_input:(m1,t1)  ~previous_output:(m2,t2) ->
      reuse m1 m2, join_tracked t1 t2
end

include Domain

let multidim_hook (module Abstract: Abstractions.S) : (module Abstractions.S) =
  match Abstract.Val.get Main_values.CVal.key, Abstract.Dom.get key with
  | None, _
  | _, None -> (module Abstract)
  | Some get_cval,  Some get_multidim ->
    let module Eval =
      Evaluation.Make (Abstract.Val) (Abstract.Loc) (Abstract.Dom)
    in
    let module Dom = struct
      include Abstract.Dom

      let join a b =
        let r = join (set key Domain.top a) (set key Domain.top b) in
        let oracle state exp = (* TODO: cache results *)
          let v, _alarms = Eval.evaluate state exp in
          match v with
          | `Bottom -> Cvalue.V.top
          | `Value (_valuation,v) -> get_cval v
        in
        let oracle = function
          | Abstract_memory.Left ->  convert_oracle (oracle a)
          | Abstract_memory.Right -> convert_oracle (oracle b)
        in
        let multidim = Domain.join' ~oracle (get_multidim a) (get_multidim b) in
        set key multidim r
    end
    in
    (module struct
      module Val = Abstract.Val
      module Loc = Abstract.Loc
      module Dom = Dom
    end)

(* Registers the domain. *)
let flag =
  let name = "multidim"
  and descr = "Improve the precision over arrays of structures \
               or multidimensional arrays."
  and experimental = true
  and abstraction =
    Abstractions.{ values = Single (module Main_values.CVal);
                   domain = Domain (module Domain); }
  in
  Abstractions.register ~name ~descr ~experimental abstraction

let () = Abstractions.register_hook multidim_hook
