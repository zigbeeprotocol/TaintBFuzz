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

open Abstract_interp
open Lattice_bounds
open Bottom.Operators

let emitter = Lattice_messages.register "Ival"
let log_imprecision s = Lattice_messages.emit_imprecision emitter s

module type Type = sig
  (* Binary abstract operations do not model precisely float/integer operations.
     It is the responsibility of the callers to have two operands of the same
     implicit type. The only exception is for [singleton_zero], which is the
     correct representation of [0.] *)
  type t = private
    | Bottom
    | Int of Int_val.t
    | Float of Fval.t

  val bottom: t
  val zero: t
  val one: t
  val top: t
  val inject_singleton: Int.t -> t
  val inject_int: Int_val.t -> t
  val inject_float: Fval.t -> t
  val inject_float_interval: float -> float -> t
end

(* This module ensures that small integer singletons (and especially zero) and
   the top value are shared in memory. This enables some optimizations where we
   check the physical identity instead of the equality. Outside this module,
   values of type t can only be created by calling [inject_] constructors. *)
module Type : Type = struct
  type t =
    | Bottom
    | Int of Int_val.t
    | Float of Fval.t

  let small_nums =
    Array.init 33 (fun i -> Int (Int_val.inject_singleton (Int.of_int i)))

  let bottom = Bottom
  let zero = small_nums.(0)
  let one = small_nums.(1)
  let top = Int Int_val.top

  let inject_singleton e =
    if Int.le Int.zero e && Int.le e Int.thirtytwo
    then small_nums.(Int.to_int_exn e)
    else Int (Int_val.inject_singleton e)

  let inject_int i =
    try
      let e = Int_val.project_int i in
      if Int.le Int.zero e && Int.le e Int.thirtytwo
      then small_nums.(Int.to_int_exn e)
      else Int i
    with Int_val.Not_Singleton ->
      if Int_val.(equal top i) then top else Int i

  let inject_float f =
    if Fval.(equal plus_zero f)
    then zero
    else Float f

  let inject_float_interval flow fup =
    let flow = Fval.F.of_float flow in
    let fup = Fval.F.of_float fup in
    (* make sure that zero float is also zero int *)
    if Fval.F.equal Fval.F.plus_zero flow && Fval.F.equal Fval.F.plus_zero fup
    then zero
    else Float (Fval.inject Fval.Double flow fup)
end

include Type

module Widen_Hints = Datatype.Integer.Set
type size_widen_hint = Integer.t
type numerical_widen_hint = Widen_Hints.t * Fc_float.Widen_Hints.t
type widen_hint = size_widen_hint * numerical_widen_hint

let hash = function
  | Bottom -> 311
  | Int i -> Int_val.hash i
  | Float f -> 3 + 17 * Fval.hash f

let compare e1 e2 =
  if e1==e2 then 0 else
    match e1, e2 with
    | Bottom, Bottom -> 0
    | Int i1, Int i2 -> Int_val.compare i1 i2
    | Float f1, Float f2 -> Fval.compare f1 f2
    | _, Bottom -> 1
    | Bottom, _ -> -1
    | _, Int _ -> 1
    | Int _, _ -> -1

let equal e1 e2 = compare e1 e2 = 0

let pretty fmt = function
  | Bottom -> Format.fprintf fmt "BottomMod"
  | Int i -> Int_val.pretty fmt i
  | Float f -> Fval.pretty fmt f


let cardinal_zero_or_one = function
  | Bottom -> true
  | Int i -> Int_val.cardinal_zero_or_one i
  | Float f -> Fval.is_singleton f

let is_singleton_int = function
  | Bottom -> false
  | Float _ -> false
  | Int i -> Int_val.is_singleton i

let is_bottom = (==) bottom
let is_zero = (==) zero
let is_one = (==) one

let minus_one = inject_int Int_val.minus_one
let zero_or_one = inject_int Int_val.zero_or_one
let float_zeros = inject_float Fval.zeros

let positive_integers = inject_int Int_val.positive_integers
let negative_integers = inject_int Int_val.negative_integers

let inject_int_or_bottom = function
  | `Bottom -> bottom
  | `Value i -> inject_int i

(*  let minus_zero = Float (Fval.minus_zero, Fval.minus_zero) *)

let project_float v =
  if is_zero v
  then Fval.plus_zero
  else
    match v with
    | Float f -> f
    | Bottom | Int _ -> assert false (* by hypothesis that it is a float *)

let is_float = function
  | Bottom | Float _ -> true
  | Int _ as i -> equal zero i

let is_int = function
  | Bottom | Int _ -> true
  | Float _ -> false

let contains_zero = function
  | Bottom -> false
  | Int i -> Int_val.contains_zero i
  | Float f -> Fval.contains_a_zero f

let contains_non_zero = function
  | Bottom -> false
  | Int i -> Int_val.contains_non_zero i
  | Float f -> Fval.contains_non_zero f


exception Not_Singleton_Int = Int_val.Not_Singleton

let project_int_val = function
  | Int i -> Some i
  | Bottom | Float _ -> None

let project_int = function
  | Int i -> Int_val.project_int i
  | Bottom | Float _ -> raise Not_Singleton_Int

let is_small_set = function
  | Bottom -> true
  | Int i -> Int_val.is_small_set i
  | Float _ -> false

let project_small_set = function
  | Bottom -> Some []
  | Int i -> Int_val.project_small_set i
  | Float _ -> None

let cardinal = function
  | Bottom -> Some Int.zero
  | Int i -> Int_val.cardinal i
  | Float f -> if Fval.is_singleton f then Some Int.one else None

let cardinal_estimate v ~size =
  match v with
  | Bottom -> Int.zero
  | Int i -> Int_val.cardinal_estimate ~size i
  | Float f ->
    if Fval.is_singleton f
    then Int.one
    else
      let bits_of_float =
        if Integer.(equal size (of_int 32))
        then Fval.bits_of_float32_list
        else if Integer.(equal size (of_int 64))
        then Fval.bits_of_float64_list
        else (fun _ -> [Int.zero, Int.pred (Int.two_power size)])
      in
      let bits_list = bits_of_float f in
      let count acc (min, max) = Int.add acc (Int.length min max) in
      List.fold_left count Int.zero bits_list

let cardinal_less_than v n =
  match v with
  | Bottom -> 0
  | Int i -> Int_val.cardinal_less_than i n
  | Float f -> if Fval.is_singleton f then 1 else raise Not_less_than

let cardinal_is_less_than v n =
  match cardinal v with
  | None -> false
  | Some c -> Int.le c (Int.of_int n)

let inject_top min max rem modu =
  match min, max with
  | Some mn, Some mx when Int.gt mn mx -> bottom
  | _, _ -> inject_int (Int_val.make ~min ~max ~rem ~modu)

let inject_interval ~min ~max ~rem ~modu =
  match min, max with
  | Some mn, Some mx when Int.gt mn mx -> bottom
  | _, _ -> inject_int (Int_val.inject_interval ~min ~max ~rem ~modu)

let subdivide ~size = function
  | Bottom -> raise Can_not_subdiv
  | Float fval ->
    let fkind = match Integer.to_int_exn size with
      | 32 -> Fval.Single
      | 64 -> Fval.Double
      | _ -> raise Can_not_subdiv (* see Value/Value#105 *)
    in
    let f1, f2 = Fval.subdiv_float_interval fkind fval in
    inject_float f1, inject_float f2
  | Int i ->
    let i1, i2 = Int_val.subdivide i in
    inject_int i1, inject_int i2

let inject_range min max = inject_top min max Int.zero Int.one

let top_float = inject_float Fval.top
let top_single_precision_float = inject_float Fval.top


let min_max_r_mod = function
  | Bottom -> raise Error_Bottom
  | Int i -> Int_val.min_max_rem_modu i
  | Float _ -> None, None, Int.zero, Int.one

let min_and_max = function
  | Bottom -> raise Error_Bottom
  | Int i -> Int_val.min_and_max i
  | Float _ -> None, None

let min_and_max_float t =
  match t with
  | Int _ when is_zero t -> Some (Fval.F.plus_zero, Fval.F.plus_zero), false
  | Float f -> Fval.min_and_max f
  | _ -> assert false

let has_greater_min_bound t1 t2 =
  if is_float t1 && is_float t2
  then Fval.has_greater_min_bound (project_float t1) (project_float t2)
  else
    let m1, _ = min_and_max t1 in
    let m2, _ = min_and_max t2 in
    match m1, m2 with
    | None, None -> 0
    | None, Some _ -> -1
    | Some _, None -> 1
    | Some m1, Some m2 -> Int.compare m1 m2

let has_smaller_max_bound t1 t2 =
  if is_float t1 && is_float t2
  then Fval.has_smaller_max_bound (project_float t1) (project_float t2)
  else
    let _, m1 = min_and_max t1 in
    let _, m2 = min_and_max t2 in
    match m1, m2 with
    | None, None -> 0
    | None, Some _ -> -1
    | Some _, None -> 1
    | Some m1, Some m2 -> Int.compare m2 m1

let widen (bitsize,(wh,fh)) t1 t2 =
  if equal t1 t2 || cardinal_zero_or_one t1 || is_bottom t1 then t2
  else
    match t2 with
    | Bottom -> t2
    | Float f2 ->
      let f1 = project_float t1 in
      let prec =
        if Integer.equal bitsize (Integer.of_int 32)
        then Float_sig.Single
        else if Integer.equal bitsize (Integer.of_int 64)
        then Float_sig.Double
        else if Integer.equal bitsize (Integer.of_int 128)
        then Float_sig.Long_Double
        else Float_sig.Single
      in
      inject_float (Fval.widen fh prec f1 f2)
    | Int i2 ->
      let i1 = match t1 with
        | Bottom -> assert false
        | Int i1 -> i1
        | Float _ -> Int_val.top
      in
      inject_int (Int_val.widen (bitsize,wh) i1 i2)

let meet v1 v2 =
  if v1 == v2 then v1 else
    let result =
      match v1, v2 with
      | Bottom, _ | _, Bottom -> bottom
      | Int i1, Int i2 -> inject_int_or_bottom (Int_val.meet i1 i2)
      | Float f1, Float f2 -> begin
          match Fval.meet f1 f2 with
          | `Value f -> inject_float f
          | `Bottom -> bottom
        end
      | (Float f as ff), (Int _ as o)
      | (Int _ as o), (Float f as ff) ->
        if equal o top then ff
        else if contains_zero o && Fval.contains_plus_zero f then zero
        else bottom
    in
    (*      Format.printf "meet: %a /\\ %a -> %a@\n"
            pretty v1 pretty v2 pretty result;*)
    result

let intersects v1 v2 =
  v1 == v2 ||
  match v1, v2 with
  | Bottom, _ | _, Bottom -> false
  | Int i1, Int i2 -> Int_val.intersects i1 i2
  | Float f1, Float f2 -> begin
      match Fval.forward_comp Comp.Eq f1 f2 with
      | Comp.False -> false
      | Comp.True | Comp.Unknown -> true
    end
  | Float f, other | other, Float f ->
    equal top other || (Fval.contains_plus_zero f && contains_zero other)

let narrow v1 v2 =
  if v1 == v2 then v1 else
    match v1, v2 with
    | Bottom, _ | _, Bottom -> bottom
    | Float _, Float _ -> meet v1 v2 (* meet is exact *)
    | v, (Int _ as t) when equal t top -> v
    | (Int _ as t), v when equal t top -> v
    | Int i1, Int i2 -> inject_int_or_bottom (Int_val.narrow i1 i2)
    | Float f, (Int _ as s) | (Int _ as s), Float f when is_zero s -> begin
        match Fval.narrow f Fval.zeros with
        | `Value f -> inject_float f
        | `Bottom -> bottom
      end
    | Float _, Int _ | Int _, Float _ ->
      (* ill-typed case. It is better to keep the operation symmetric *)
      top

let link v1 v2 = match v1, v2 with
  | Int i1, Int i2 -> inject_int (Int_val.link i1 i2)
  | _ -> bottom

let join v1 v2 =
  if v1 == v2 then v1 else
    match v1, v2 with
    | Bottom, t | t, Bottom -> t
    | Int i1, Int i2 -> inject_int (Int_val.join i1 i2)
    | Float f1, Float f2 -> inject_float (Fval.join f1 f2)
    | Float f as ff, other | other, (Float f as ff) ->
      if is_zero other
      then inject_float (Fval.join Fval.plus_zero f)
      else if is_bottom other then ff
      else top

let complement_int_under ~size ~signed = function
  | Bottom | Float _ -> `Bottom
  | Int i -> Int_val.complement_under ~size ~signed i >>-: inject_int

let fold_int f v acc =
  match v with
  | Bottom -> acc
  | Float _ -> raise Error_Top
  | Int i -> Int_val.fold_int f i acc

let fold_int_decrease f v acc =
  match v with
  | Bottom -> acc
  | Float _ -> raise Error_Top
  | Int i -> Int_val.fold_int ~increasing:false f i acc

let fold_enum f v acc =
  match v with
  | Bottom -> acc
  | Float fl when Fval.is_singleton fl -> f v acc
  | Float _ -> raise Error_Top
  | Int _ -> fold_int (fun x acc -> f (inject_singleton x) acc) v acc

let is_included t1 t2 =
  (t1 == t2) ||
  match t1, t2 with
  | Bottom, _ -> true
  | _, Bottom -> false
  | Int i1, Int i2 -> Int_val.is_included i1 i2
  | Float f1, Float f2 -> Fval.is_included f1 f2
  | Float _, _ -> equal t2 top
  | Int i, Float f -> Int_val.is_zero i && Fval.contains_plus_zero f

let add_singleton_int i = function
  | Bottom -> bottom
  | Float _ -> assert false
  | Int itv -> inject_int (Int_val.add_singleton i itv)

let add_int v1 v2 =
  match v1, v2 with
  | Bottom, _ | _, Bottom -> bottom
  | Float _, _ | _, Float _ -> assert false
  | Int i1, Int i2 -> inject_int (Int_val.add i1 i2)

let add_int_under v1 v2 =
  match v1, v2 with
  | Bottom, _ | _, Bottom -> bottom
  | Float _, _ | _, Float _ -> assert false
  | Int i1, Int i2 -> inject_int_or_bottom (Int_val.add_under i1 i2)

let neg_int = function
  | Bottom -> bottom
  | Float _ -> assert false
  | Int i -> inject_int (Int_val.neg i)

let abs_int = function
  | Bottom -> bottom
  | Float _ -> assert false
  | Int i -> inject_int (Int_val.abs i)

let sub_int v1 v2 = add_int v1 (neg_int v2)
let sub_int_under v1 v2 = add_int_under v1 (neg_int v2)

let min_int = function
  | Bottom -> raise Error_Bottom
  | Int i -> fst (Int_val.min_and_max i)
  | Float _ -> None

let max_int = function
  | Bottom -> raise Error_Bottom
  | Int i -> snd (Int_val.min_and_max i)
  | Float _ -> None


(* TODO: rename this function to scale_int *)
let scale f v =
  if Int.is_zero f
  then zero
  else
    match v with
    | Bottom -> bottom
    | Float _ -> top
    | Int i -> inject_int (Int_val.scale f i)

let scale_div ~pos f = function
  | Bottom -> bottom
  | Int i -> inject_int (Int_val.scale_div ~pos f i)
  | Float _ -> top

let scale_div_under ~pos f = function
  | Bottom -> bottom
  | Int i -> inject_int_or_bottom (Int_val.scale_div_under ~pos f i)
  | Float _ -> bottom

let div v1 v2 =
  match v1, v2 with
  | Bottom, _ | _, Bottom -> bottom
  | Int i1, Int i2 -> inject_int_or_bottom (Int_val.div i1 i2)
  | Float _, _ | _, Float _ -> assert false

(* [scale_rem ~pos:false f v] is an over-approximation of the set of
   elements [x mod f] for [x] in [v].

   [scale_rem ~pos:true f v] is an over-approximation of the set of
   elements [x e_rem f] for [x] in [v].
*)
let scale_rem ~pos f v =
  if Int.is_zero f then bottom
  else
    match v with
    | Bottom -> bottom
    | Int i -> inject_int (Int_val.scale_rem ~pos f i)
    | Float _ -> top

let c_rem v1 v2 =
  match v1, v2 with
  | Bottom, _ | _, Bottom -> bottom
  | Float _, _ | _, Float _ -> top
  | Int i1, Int i2 -> inject_int_or_bottom (Int_val.c_rem i1 i2)

let create_all_values ~signed ~size =
  inject_int (Int_val.create_all_values ~signed ~size)

let big_int_64 = Int.of_int 64
let big_int_32 = Int.thirtytwo

let cast_int_to_int ~size ~signed = function
  | Bottom -> bottom
  | Int i -> inject_int (Int_val.cast_int_to_int ~size ~signed i)
  | Float _ -> assert false

let reinterpret_float_as_int ~signed ~size f =
  let reinterpret_list l =
    let reinterpret_one (b, e) =
      let i = inject_range (Some b) (Some e) in
      cast_int_to_int ~size ~signed i
    in
    let l = List.map reinterpret_one l in
    List.fold_left join bottom l
  in
  if Int.equal size big_int_64
  then
    let itvs = Fval.bits_of_float64_list f in
    reinterpret_list itvs
  else
  if Int.equal size big_int_32
  then
    let itvs = Fval.bits_of_float32_list f in
    reinterpret_list itvs
  else top

let reinterpret_as_int ~size ~signed i =
  match i with
  | Bottom -> bottom
  | Int _ ->
    (* On integers, cast and reinterpretation are the same operation *)
    cast_int_to_int ~signed ~size i
  | Float f -> reinterpret_float_as_int ~signed ~size f

let cast_float_to_float fkind v =
  match v with
  | Bottom -> bottom
  | Float f ->
    begin match fkind with
      | Fval.Real | Fval.Long_Double | Fval.Double -> v
      | Fval.Single ->
        inject_float (Fval.round_to_single_precision_float f)
    end
  | Int _ when is_zero v -> zero
  | Int _ -> top_float


(* TODO rename to mul_int *)
let mul v1 v2 =
  if is_one v1 then v2
  else if is_zero v2 || is_zero v1 then zero
  else if is_one v2 then v1
  else
    match v1, v2 with
    | Bottom, _ | _, Bottom -> bottom
    | Float _, _ | _, Float _ -> top
    | Int i1, Int i2 -> inject_int (Int_val.mul i1 i2)

let shift_right v1 v2 =
  match v1, v2 with
  | Bottom, _ | _, Bottom -> bottom
  | Int i1, Int i2 -> inject_int_or_bottom (Int_val.shift_right i1 i2)
  | _, _ -> top

let shift_left v1 v2 =
  match v1, v2 with
  | Bottom, _ | _, Bottom -> bottom
  | Int i1, Int i2 -> inject_int_or_bottom (Int_val.shift_left i1 i2)
  | _, _ -> top


let interp_boolean ~contains_zero ~contains_non_zero =
  match contains_zero, contains_non_zero with
  | true, true -> zero_or_one
  | true, false -> zero
  | false, true -> one
  | false, false -> bottom


module Infty = struct
  let lt0 = function
    | None -> true
    | Some a -> Int.lt a Int.zero

  let div a b = match a with
    | None -> None
    | Some a -> match b with
      | None -> Some Int.zero
      | Some b -> Some (Int.e_div a b)

  let neg = function
    | Some a -> Some (Int.neg a)
    | None -> None
end

let backward_mult_pos_left min_right max_right result =
  let min_res, max_res = min_and_max result in
  let min_left =
    Infty.div min_res (if Infty.lt0 min_res then Some min_right else max_right)
  and max_left =
    Infty.div max_res (if Infty.lt0 max_res then max_right else Some min_right)
  in
  inject_range min_left max_left

let backward_mult_neg_left min_right max_right result =
  backward_mult_pos_left (Integer.neg max_right) (Infty.neg min_right) (neg_int result)

let backward_mult_int_left ~right ~result =
  match min_and_max right with
  | None, None -> `Value None
  | Some a, Some b when a > b -> `Bottom

  | Some a, Some b when a = Int.zero && b = Int.zero ->
    if contains_zero result then `Value None else `Bottom

  | Some a, max when a > Int.zero ->
    `Value (Some (backward_mult_pos_left a max result))

  | Some a, max when a >= Int.zero ->
    if contains_zero result
    then `Value None
    else `Value (Some (backward_mult_pos_left Int.one max result))

  | min, Some b when b < Int.zero ->
    `Value (Some (backward_mult_neg_left min b result))

  | min, Some b when b = Int.zero ->
    if contains_zero result
    then `Value None
    else `Value (Some (backward_mult_neg_left min Int.minus_one result))

  | min, max ->
    if contains_zero result
    then `Value None
    else
      `Value (Some (join
                      (backward_mult_pos_left Int.one max result)
                      (backward_mult_neg_left min Int.one result)))


let backward_le_int max v =
  match v with
  | Bottom -> bottom
  | Float _ -> v
  | Int _ -> narrow v (inject_int (Int_val.inject_range None max))

let backward_ge_int min v =
  match v with
  | Bottom -> bottom
  | Float _ -> v
  | Int _ -> narrow v (inject_int (Int_val.inject_range min None))

let backward_lt_int max v = backward_le_int (Option.map Int.pred max) v
let backward_gt_int min v = backward_ge_int (Option.map Int.succ min) v

let diff_if_one value rem =
  match value, rem with
  | Int i1, Int i2 -> inject_int_or_bottom (Int_val.diff_if_one i1 i2)
  | _, _ -> value

let diff value rem =
  log_imprecision "Ival.diff";
  diff_if_one value rem

(* This function is an iterator, but it needs [diff_if_one] just above. *)
let fold_int_bounds f v acc =
  match v with
  | Bottom -> acc
  | Float _ -> f v acc
  | Int _ ->
    if cardinal_zero_or_one v then f v acc
    else
      (* apply [f] to [b] and reduce [v] if [b] is finite,
         or return [v] and [acc] unchanged *)
      let on_bound b v acc = match b with
        | None -> v, acc
        | Some b ->
          let b = inject_singleton b in
          diff_if_one v b, f b acc
      in
      let min, max = min_and_max v in
      (* [v] has cardinal at least 2, so [min] and [max] are distinct *)
      let v, acc = on_bound min v acc in
      let v, acc = on_bound max v acc in
      (* but if the cardinal was 2, then this [v] may be bottom *)
      if equal v bottom then acc else f v acc


let backward_comp_int_left op l r =
  let open Comp in
  try
    match op with
    | Le -> backward_le_int (max_int r) l
    | Ge -> backward_ge_int (min_int r) l
    | Lt -> backward_lt_int (max_int r) l
    | Gt -> backward_gt_int (min_int r) l
    | Eq -> narrow l r
    | Ne -> diff_if_one l r
  with Error_Bottom (* raised by max_int *) -> bottom

let backward_comp_float_left_true op fkind f1 f2  =
  let f1 = project_float f1 in
  let f2 = project_float f2 in
  begin match Fval.backward_comp_left_true op fkind f1 f2 with
    | `Value f -> inject_float f
    | `Bottom -> bottom
  end

let backward_comp_float_left_false op fkind f1 f2  =
  let f1 = project_float f1 in
  let f2 = project_float f2 in
  begin match Fval.backward_comp_left_false op fkind f1 f2 with
    | `Value f -> inject_float f
    | `Bottom -> bottom
  end



let rec extract_bits ~start ~stop ~size v =
  match v with
  | Bottom -> bottom
  | Int i -> inject_int (Int_val.extract_bits ~start ~stop i)
  | Float f ->
    let inject (b, e) = inject_range (Some b) (Some e) in
    let itvs =
      if Int.equal size big_int_64 then
        List.map inject (Fval.bits_of_float64_list f)
      else if Int.equal size big_int_32 then
        List.map inject (Fval.bits_of_float32_list f)
      else (* long double *)
        [top]
    in
    let bits = List.map (extract_bits ~start ~stop ~size) itvs in
    List.fold_left join bottom bits

let all_values ~size v =
  if Int.lt big_int_64 size then false
  (* values of this size cannot be enumerated anyway in C.
     They may occur while initializing large blocks of arrays.
  *)
  else
    match v with
    | Bottom | Float _ -> false
    | Int i -> Int_val.all_values ~size i

let compare_min_max min max =
  match min, max with
  | None,_ -> -1
  | _,None -> -1
  | Some min, Some max -> Int.compare min max

let compare_max_min max min =
  match max, min with
  | None,_ -> 1
  | _,None -> 1
  | Some max, Some min -> Int.compare max min

let forward_le_int i1 i2 =
  if compare_max_min (max_int i1) (min_int i2) <= 0 then Comp.True
  else if compare_min_max (min_int i1) (max_int i2) > 0 then Comp.False
  else Comp.Unknown

let forward_lt_int i1 i2 =
  if compare_max_min (max_int i1) (min_int i2) < 0 then Comp.True
  else if compare_min_max (min_int i1) (max_int i2) >= 0 then Comp.False
  else Comp.Unknown

let forward_eq_int i1 i2 =
  if cardinal_zero_or_one i1 && equal i1 i2 then Comp.True
  else if intersects i2 i2 then Comp.Unknown
  else Comp.False

let forward_comp_int op i1 i2 =
  let open Abstract_interp.Comp in
  match op with
  | Le -> forward_le_int i1 i2
  | Ge -> forward_le_int i2 i1
  | Lt -> forward_lt_int i1 i2
  | Gt -> forward_lt_int i2 i1
  | Eq -> forward_eq_int i1 i2
  | Ne -> inv_truth (forward_eq_int i1 i2)

let rehash = function
  | Bottom -> bottom
  | Int i -> inject_int i
  | Float f -> inject_float f

include (
  Datatype.Make_with_collections
    (struct
      type ival = t
      type t = ival
      let name = Int.name ^ " lattice_mod"
      open Structural_descr
      let structural_descr =
        t_sum
          [| [| Int_val.packed_descr |];
             [| Fval.packed_descr |] |]
      let reprs = [ top ; bottom ]
      let equal = equal
      let compare = compare
      let hash = hash
      let pretty = pretty
      let rehash = rehash
      let internal_pretty_code = Datatype.pp_fail
      let mem_project = Datatype.never_any_project
      let copy = Datatype.undefined
      let varname = Datatype.undefined
    end):
    Datatype.S_with_collections with type t := t)

let scale_int_base factor v = match factor with
  | Int_Base.Top -> top
  | Int_Base.Value f -> scale f v

type overflow_float_to_int =
  | FtI_Ok of Int.t (* Value in range *)
  | FtI_Overflow of Floating_point.sign (* Overflow in the corresponding
                                           direction *)

let cast_float_to_int_non_nan ~signed ~size (min, max) =
  let all = create_all_values ~size ~signed in
  let min_all = Option.get (min_int all) in
  let max_all = Option.get (max_int all) in
  let conv f =
    try
      (* truncate_to_integer returns an integer that fits in a 64 bits
         integer, but might not fit in [size, sized] *)
      let i = Floating_point.truncate_to_integer f in
      if Int.ge i min_all then
        if Int.le i max_all then FtI_Ok i
        else FtI_Overflow Floating_point.Pos
      else FtI_Overflow Floating_point.Neg
    with Floating_point.Float_Non_representable_as_Int64 sign ->
      FtI_Overflow sign
  in
  let min_int = conv (Fval.F.to_float min) in
  let max_int = conv (Fval.F.to_float max) in
  match min_int, max_int with
  | FtI_Ok min_int, FtI_Ok max_int -> (* no overflow *)
    inject_range (Some min_int) (Some max_int)

  | FtI_Overflow Floating_point.Neg, FtI_Ok max_int -> (* one overflow *)
    inject_range (Some min_all) (Some max_int)
  | FtI_Ok min_int, FtI_Overflow Floating_point.Pos -> (* one overflow *)
    inject_range (Some min_int) (Some max_all)

  (* two overflows *)
  | FtI_Overflow Floating_point.Neg, FtI_Overflow Floating_point.Pos ->
    inject_range (Some min_all) (Some max_all)

  (* Completely out of range *)
  | FtI_Overflow Floating_point.Pos, FtI_Overflow Floating_point.Pos
  | FtI_Overflow Floating_point.Neg, FtI_Overflow Floating_point.Neg ->
    bottom

  | FtI_Overflow Floating_point.Pos, FtI_Overflow Floating_point.Neg
  | FtI_Overflow Floating_point.Pos, FtI_Ok _
  | FtI_Ok _, FtI_Overflow Floating_point.Neg ->
    assert false (* impossible if min-max are correct *)

let cast_float_to_int ~signed ~size iv =
  if equal top iv then top
  else
    match Fval.min_and_max (project_float iv) with
    | Some (min, max), _nan -> cast_float_to_int_non_nan ~signed ~size (min, max)
    | None, _ -> bottom (* means NaN *)


(* These are the bounds of the range of integers that can be represented
   exactly as 64 bits double values *)
let double_min_exact_integer = Int.neg (Int.two_power_of_int 53)
let double_max_exact_integer = Int.two_power_of_int 53

(* same with 32 bits single values *)
let single_min_exact_integer = Int.neg (Int.two_power_of_int 24)
let single_max_exact_integer = Int.two_power_of_int 24

(* Same values expressed as double *)
let double_min_exact_integer_d = -. (2. ** 53.)
let double_max_exact_integer_d =     2. ** 53.
let single_min_exact_integer_d = -. (2. ** 24.)
let single_max_exact_integer_d =     2. ** 24.


(* finds all floating-point values [f] such that casting [f] to an integer
   type returns [i]. *)
let cast_float_to_int_inverse ~single_precision i =
  let exact_min, exact_max =
    if single_precision
    then single_min_exact_integer, single_max_exact_integer
    else double_min_exact_integer, double_max_exact_integer
  in
  let fkind = if single_precision then Fval.Single else Fval.Double in
  match min_and_max i with
  | Some min, Some max when Int.lt exact_min min && Int.lt max exact_max ->
    let minf =
      if Int.le min Int.zero then
        (* min is negative. We want to return [(float)((real)(min-1)+epsilon)],
           as converting this number to int will truncate all the fractional
           part (C99 6.3.1.4). Given [exact_min] and [exact_max], 1ulp
           is at most 1 here, so adding 1ulp will at most cancel the -1.
           Hence, we can use [next_float]. *)
        (* This float is finite because min is small enough *)
        Fval.F.next_float fkind (Int.to_float (Int.pred min))
      else (* min is positive. Since casting truncates towards 0,
              [(int)((real)min-epsilon)] would return [min-1]. Hence, we can
              simply return the float corresponding to [min] -- which can be
              represented precisely given [exact_min] and [exact_max]. *)
        Int.to_float min
    in
    (* All operations are dual w.r.t. the min bound. *)
    let maxf =
      if Int.le Int.zero max
      then
        (* This float is finite because max is big enough *)
        Fval.F.prev_float fkind (Int.to_float (Int.succ max))
      else Int.to_float max
    in
    assert (Fval.F.is_finite (Fval.F.of_float minf));
    assert (Fval.F.is_finite (Fval.F.of_float maxf));
    inject_float (Fval.inject fkind (Fval.F.of_float minf) (Fval.F.of_float maxf))
  | _ -> if single_precision then top_single_precision_float else top_float


let cast_int_to_float_inverse_not_nan ~single_precision (min, max) =
  (* We restrict ourselves to (min,max) \in [exact_min, exact_max]. Outside of
     this range, the conversion int -> float is not exact, and the operation
     is more involved. *)
  let exact_min, exact_max =
    if single_precision
    then single_min_exact_integer_d, single_max_exact_integer_d
    else double_min_exact_integer_d, double_max_exact_integer_d
  in
  (* We find the integer range included in [f] *)
  let min = Fval.F.to_float min in
  let max = Fval.F.to_float max in
  if exact_min <= min && max <= exact_max then
    (* Round to integers in the proper direction: discard the non-floating-point
       values on each extremity. *)
    let min = ceil min in
    let max = floor max in
    let conv f = try  Some (Integer.of_float f) with Z.Overflow -> None in
    let r = inject_range (conv min) (conv max) in
    (* Kernel.result "Cast I->F inv:  %a -> %a@." pretty f pretty r; *)
    r
  else top (* Approximate *)

let cast_int_to_float_inverse ~single_precision f =
  match min_and_max_float f with
  | None, _ -> (* NaN *) bottom (* a cast of NaN to int is fully undefined *)
  | Some (min, max), _ (*we can disregard the NaN boolean for the same reason *)
    ->
    cast_int_to_float_inverse_not_nan ~single_precision (min, max)

let of_int i = inject_singleton (Int.of_int i)
let of_int64 i = inject_singleton (Int.of_int64 i)


(* This function always succeeds without alarms for C integers, because they
   always fit within a float32. *)
let cast_int_to_float fkind v =
  let min,max = min_and_max v in
  inject_float (Fval.cast_int_to_float fkind min max)

let reinterpret_as_float kind i =
  match i with
  | Bottom -> bottom
  | Float _ ->  i
  | Int _ when is_zero i || is_bottom i -> i
  | Int _ ->
    (* Reinterpret a range of integers as a range of floats.
       Float are ordered this way :
       if [min_i], [max_i] are the bounds of the signed integer type that
       has the same number of bits as the floating point type, and [min_f]
       [max_f] are the integer representation of the most negative and most
       positive finite float of the type, and < is signed integer comparison,
       we have: min_i < min_f <  min_f+1  < -1 <  0 < max_f <  max_f+1  < max_i
                 |        |       |          |    |      |       |          |
                 --finite--       -not finite-    -finite-       -not finite-
                 |        |       |<--------->    |      |       |<--------->
                -0.     -max    -inf   NaNs      +0.    max     inf   NaNs
       The float are of the same sign as the integer they convert into.
       Furthermore, the conversion function is increasing on the positive
       interval, and decreasing on the negative one. *)
    let reinterpret size kind conv min_f max_f =
      let size = Integer.of_int size in
      let i = cast_int_to_int ~size ~signed:true i in
      (* Intersect [i'] with [i], and return the (finite) bounds directly. *)
      let bounds_narrow i' =
        let r = narrow i i' in
        if is_bottom r then `Bottom
        else
          match min_and_max r with
          | None, _ | _, None -> assert false (* i is finite thanks to cast *)
          | Some b, Some e -> `Value (b, e)
      in
      let s_max_f = Int.succ max_f (* neg inf *) in
      let s_min_f = Int.succ min_f (* pos inf *) in
      let s_s_max_f = Int.succ s_max_f (* first 'positive' NaN *) in
      let s_s_min_f = Int.succ s_min_f (* first 'negative' NaN  *) in
      (* positive floats *)
      let f_pos = inject_range (Some Integer.zero) (Some s_max_f) in
      (* negative floats *)
      let f_neg = inject_range None (Some s_min_f) in
      (* 'positive' NaNs *)
      let nan_pos = inject_range (Some s_s_max_f) None in
      (* 'negative' NaNs *)
      let nan_neg = inject_range (Some s_s_min_f) (Some Int.minus_one) in
      let nan = (* at least one NaN somewhere *)
        if intersects i nan_pos || intersects i nan_neg
        then [`Value Fval.nan]
        else []
      in
      let range mn mx = Fval.inject kind (conv mn) (conv mx) in
      (* convert positive floats; increasing on positive range *)
      let pos = bounds_narrow f_pos >>-: (fun (b, e) -> range b e) in
      (* convert negative floats; decreasing on negative range *)
      let neg = bounds_narrow f_neg >>-: (fun (b, e) -> range e b) in
      let f = Bottom.join_list Fval.join (pos :: neg :: nan) in
      inject_float (Bottom.non_bottom f)
    in
    let open Floating_point in
    match kind with
    | Cil_types.FDouble ->
      let conv v = Fval.F.of_float (Int64.float_of_bits (Int.to_int64_exn v)) in
      reinterpret
        64 Fval.Double conv bits_of_most_negative_double bits_of_max_double
    | Cil_types.FFloat ->
      let conv v = Fval.F.of_float(Int32.float_of_bits (Int.to_int32_exn v)) in
      reinterpret
        32 Fval.Single conv bits_of_most_negative_float bits_of_max_float
    | Cil_types.FLongDouble ->
      (* currently always imprecise *)
      top_float


let bitwise_int f_int v1 v2 =
  match v1, v2 with
  | Int i1, Int i2 -> inject_int (f_int i1 i2)
  | _, _ -> top

let bitwise_or = bitwise_int Int_val.bitwise_or
let bitwise_and = bitwise_int Int_val.bitwise_and
let bitwise_xor = bitwise_int Int_val.bitwise_xor

let bitwise_signed_not = function
  | Bottom -> bottom
  | Float _ -> assert false
  | Int i -> inject_int (Int_val.bitwise_signed_not i)

let bitwise_unsigned_not ~size = function
  | Bottom -> bottom
  | Float _ -> assert false
  | Int i -> inject_int (Int_val.bitwise_unsigned_not ~size i)

let bitwise_not ~size ~signed v =
  if signed then
    bitwise_signed_not v
  else
    bitwise_unsigned_not ~size v

let pretty_debug = pretty
let name = "ival"

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
