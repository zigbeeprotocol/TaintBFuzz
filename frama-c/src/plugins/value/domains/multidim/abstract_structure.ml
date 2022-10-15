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
open Abstract_memory

let no_oracle = fun _exp -> Int_val.top

(* Composition operator for compare function *)

let (<?>) c lcmp =
  if c = 0 then 0 else Lazy.force lcmp


(* ------------------------------------------------------------------------ *)
(* --- C struct abstraction                                             --- *)
(* ------------------------------------------------------------------------ *)

module type Config =
sig
  val deps : State.t list
end

module type Structure =
sig
  type t
  type submemory
  val pretty : Format.formatter -> t -> unit
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val raw : t -> Bit.t
  val of_raw : Bit.t -> t
  val weak_erase : Bit.t -> t -> t
  val is_included : t -> t -> bool
  val unify : (submemory -> submemory -> submemory) -> t -> t -> t
  val read : t -> Cil_types.fieldinfo -> submemory
  val update : (submemory -> submemory or_bottom) -> t -> Cil_types.fieldinfo ->
    t or_bottom
  val map : (submemory -> submemory) -> t -> t
end

module Make (Config : Config) (M : ProtoMemory) =
struct
  module Field =
  struct
    include Cil_datatype.Fieldinfo
    let id f = f.Cil_types.forder (* At each node, all fields come from the same comp *)
  end
  module Values =
  struct
    include Datatype.Make (
      struct
        include Datatype.Serializable_undefined
        include M
        let name = "Abstract_Memory.Structure.Values"
        let reprs = [ of_raw Bit.zero ]
      end)
    let pretty_debug = pretty
  end
  module Initial_Values = struct let v = [[]] end
  module Deps = struct let l = Config.deps end

  module FieldMap =
    Hptmap.Make (Field) (Values) (Hptmap.Comp_unused) (Initial_Values) (Deps)

  type t = {
    padding: Bit.t;
    fields: FieldMap.t;
  }

  type submemory = M.t

  let pretty fmt m =
    Pretty_memory.pp_iter2 ~format:"@[<hv>.%a%a@]"
      FieldMap.iter Field.pretty M.pretty fmt m.fields

  let hash m =
    Hashtbl.hash (m.padding, FieldMap.hash m.fields)

  let equal m1 m2 =
    FieldMap.equal m1.fields m2.fields &&
    Bit.equal m1.padding m2.padding

  let compare m1 m2 =
    FieldMap.compare m1.fields m2.fields <?>
    lazy (Bit.compare m1.padding m2.padding)

  let raw m =
    FieldMap.fold (fun _ x acc -> Bit.join acc (M.raw x)) m.fields m.padding

  let of_raw m =
    { padding = m ; fields = FieldMap.empty }

  let weak_erase b m =
    {
      padding = Bit.join b m.padding ;
      fields = FieldMap.map (M.weak_erase b) m.fields ;
    }

  let is_included m1 m2 =
    Bit.is_included m1.padding m2.padding &&
    let decide_fast s t = if s == t then FieldMap.PTrue else PUnknown in
    let decide_fst _fi m1 = M.is_included m1 (M.of_raw m2.padding) in
    let decide_snd _fi m2 = M.is_included (M.of_raw m1.padding) m2 in
    let decide_both _fi m1 m2 = M.is_included m1 m2 in
    FieldMap.binary_predicate Hptmap_sig.NoCache UniversalPredicate
      ~decide_fast ~decide_fst ~decide_snd ~decide_both
      m1.fields m2.fields

  let unify f m1 m2 = (* f is not symmetric *)
    let decide_both _fi = fun m1 m2 -> Some (f m1 m2)
    and decide_left = FieldMap.Traversing (fun _fi m1 ->
        Some (f m1 (M.of_raw m2.padding)))
    and decide_right = FieldMap.Traversing (fun _fi m2 ->
        Some (f (M.of_raw m1.padding) m2))
    in
    let fields = FieldMap.merge
        ~cache:Hptmap_sig.NoCache ~symmetric:false ~idempotent:true
        ~decide_both ~decide_left ~decide_right
        m1.fields m2.fields
    in { padding = Bit.join m1.padding m2.padding ; fields }

  let read m fi =
    try
      FieldMap.find fi m.fields
    with Not_found -> (* field undefined *)
      M.of_raw m.padding

  let update f m fi =
    try
      let update' opt =
        let x = Option.value ~default:(M.of_raw m.padding) opt in
        match f x with
        | `Value v -> Some v
        | `Bottom -> raise Exit
      in
      `Value { m with fields = FieldMap.replace update' fi m.fields }
    with Exit ->
      `Bottom

  let map f m =
    { m with fields = FieldMap.map f m.fields }
end


(* ------------------------------------------------------------------------ *)
(* --- Disjunctions of structures                                       --- *)
(* ------------------------------------------------------------------------ *)

(* This abstraction focus on catching structures invariants of the form

   x.f = c₁ ⇒ ϕ₁(x)  ⋁  x.f = c₂ ⇒ ϕ₂(x)  ⋁  ...

   where f is a field, c₁, c₂, ... are constants and ϕ₁, ϕ₂, ... properties
   about the structure x.

   During the analysis, we track fields f, called keys which are assigned
   constant values. As the analysis  progresses, the set of keys is reduced each
   time we discover one of the field is actually not a key because it is
   assigned with non-singleton values. *)

module type Disjunction =
sig
  type t
  type submemory
  type structure
  val pretty : Format.formatter -> t -> unit
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val raw : t -> Bit.t
  val of_raw : Cil_types.compinfo -> Bit.t -> t
  val of_struct : Cil_types.compinfo -> structure -> t
  val to_struct : oracle:oracle -> t -> structure
  val weak_erase : Cil_types.compinfo -> Bit.t -> t -> t
  val is_included : t -> t -> bool
  val unify : oracle:bioracle -> (submemory -> submemory -> submemory) ->
    t -> t -> t
  val read : (submemory -> 'a) -> ('a -> 'a -> 'a)  ->
    t -> Cil_types.fieldinfo -> 'a
  val update : oracle:oracle -> (submemory -> submemory or_bottom) ->
    t -> Cil_types.fieldinfo -> t or_bottom
  val map : (submemory -> submemory) -> t -> t
end

module Disjunction (M : ProtoMemory)
    (S : Structure with type submemory = M.t) =
struct
  module Valuation =
  struct
    module FMap = Cil_datatype.Fieldinfo.Map
    module FSet = Cil_datatype.Fieldinfo.Set

    include FMap
    include FMap.Make (Datatype.Integer)
    let keys map = fold (fun k _ set -> FSet.add k set) map FSet.empty
  end

  module Map = (* 'a Map.t : (fi -> int) -> 'a *)
  struct
    module Info = struct let module_name = "Abstract_memory.Disjunction.Map" end
    include Datatype.Map (Map.Make (Valuation)) (Valuation) (Info)

    (* Defined only for Ocaml >= 4.11 *)
    let filter_map f m =
      fold (fun k x m -> match f k x with None -> m | Some y -> add k y m) m empty
  end

  module S = (* Structures in the disjunction *)
  struct
    include Datatype.Serializable_undefined
    include S

    let name = "Abstract_Memory.Disjunction.S"
    let reprs = [ of_raw Bit.zero ]
    let eval_key key m = M.to_singleton_int (read m key)
    let suitable_key key m = Option.is_some (eval_key key m)
    let keys_candidates ci m =
      let fields = Option.value ~default:[] ci.Cil_types.cfields in
      List.filter (fun fi -> suitable_key fi m) fields |>
      Valuation.FSet.of_list
    let evaluate keys m : Valuation.t =
      let update_key fi map =
        eval_key fi m |> (* should be Some *)
        Option.fold ~none:map ~some:(fun v -> Valuation.add fi v map)
      in
      Valuation.FSet.fold update_key keys Valuation.empty
  end

  include Map.Make (Datatype.Make (S))

  type submemory = M.t
  type structure = S.t

  let keys (m : t) = Valuation.keys (fst (Map.choose m))

  let pick (m : t) =
    match Map.choose_opt m with
    | None -> assert false (* the disjunction should never be empty *)
    | Some (k,s) -> k,s,Map.remove k m

  let pretty fmt (m : t) =
    match Map.bindings m with
    | [] -> assert false
    | [(_,s)] -> S.pretty fmt s
    | bindings ->
      let l = List.map snd bindings in
      Pretty_memory.pp_iter ~format:"@[<hv>%a@]" ~sep:" or @;<1 2>"
        List.iter S.pretty fmt l

  let hash (m : t) =
    Hashtbl.hash (Map.fold (fun _ s acc -> s :: acc) m [])

  let reevaluate ~oracle keys (m : t) : t =
    let update _k s acc =
      let merge prev =
        Extlib.merge_opt (fun () -> S.unify (M.smash ~oracle)) () (Some s) prev
      in
      Map.update (S.evaluate keys s) merge acc
    in
    Map.fold update m Map.empty

  let smash ?(oracle=no_oracle) (m : t) =
    let _k,s,m = pick m in
    Map.fold (fun _k -> S.unify (M.smash ~oracle)) m s

  let of_struct (ci : Cil_types.compinfo) (s : S.t) =
    let keys = S.keys_candidates ci s in
    Map.singleton (S.evaluate keys s) s

  let to_struct ~oracle (m : t) =
    smash ~oracle m

  let raw (m : t) : bit =
    let f _ x acc =
      Bottom.join Bit.join acc (`Value (S.raw x))
    in
    Bottom.non_bottom (Map.fold f m `Bottom) (* The map should not be empty *)

  let of_raw (ci : Cil_types.compinfo) (b : bit) : t =
    let s = S.of_raw b in
    of_struct ci s

  let weak_erase (ci : Cil_types.compinfo) (b : bit) (m : t) : t =
    (* if b is Zero, more could be done as all scalar fields might be a key *)
    (* weak_erase is probably linear in the number of join operators, so we
       weak_erase befoire joining as the join on erased memory is faster. *)
    let m = Map.map (fun m -> S.weak_erase b m) m in
    let s = smash m in
    of_struct ci s

  let is_included (m1 : t) (m2 : t) : bool  =
    (* Imprecise inclusion: we only consider inclusion of disjunctions where
       the set of field keys is the same *)
    let aux k s1 =
      match Map.find_opt k m2 with
      | None -> false
      | Some s2 -> S.is_included s1 s2
    in
    Map.for_all aux m1

  let unify ~oracle f (m1 : t) (m2 : t) =
    let keys = Valuation.FSet.inter (keys m1) (keys m2) in
    let m1 = reevaluate ~oracle:(oracle Left) keys m1
    and m2 = reevaluate ~oracle:(oracle Right) keys m2 in
    Map.union (fun _k m1 m2 -> Some (S.unify f m1 m2)) m1 m2

  let read map reduce (m : t) (fi : Cil_types.fieldinfo) =
    let aux _k s acc =
      map (S.read s fi) |>
      Option.fold ~none:Fun.id ~some:reduce acc |>
      Option.some
    in
    Option.get (Map.fold aux m None) (* If the map is not empty, result is Some *)

  let update ~oracle f (m : t) (fi : Cil_types.fieldinfo) =
    let m = Map.filter_map (fun _k s -> Bottom.to_option (S.update f s fi)) m in
    if Map.is_empty m then
      `Bottom
    else
      let is_key = Map.for_all (fun _k s -> S.suitable_key fi s) m in
      let old_keys = keys m in
      if is_key || Valuation.FSet.mem fi old_keys then
        let new_keys =
          if is_key
          then Valuation.FSet.add fi old_keys
          else Valuation.FSet.remove fi old_keys
        in
        `Value (reevaluate ~oracle new_keys m)
      else
        `Value (m)

  let map f m =
    Map.map (S.map f) m
end
