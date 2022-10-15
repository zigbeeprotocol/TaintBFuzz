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

exception Not_implemented

let no_oracle = fun _exp -> Int_val.top

(* Composition operator for compare function *)

let (<?>) c lcmp =
  if c = 0 then 0 else Lazy.force lcmp


(* ------------------------------------------------------------------------ *)
(* --- Comparison operators                                             --- *)
(* ------------------------------------------------------------------------ *)

type comparison =
  | Equal
  | Lower
  | Greater
  | LowerOrEqual
  | GreaterOrEqual
  | Uncomparable

let _comparison_symbol = function
  | Equal -> "="
  | Lower -> "<"
  | Greater -> ">"
  | LowerOrEqual -> Utf8_logic.le
  | GreaterOrEqual -> Utf8_logic.ge
  | Uncomparable -> "?"

module type Operators =
sig
  [@@@warning "-32"] (* unused operators... for now*)

  type t
  val (<) : t -> t -> bool
  val (>) : t -> t -> bool
  val (<=) : t -> t -> bool
  val (>=) : t -> t -> bool
  val (===) : t -> t -> bool
end

let operators :
  type a . (a -> a -> comparison) -> (module Operators with type t = a) =
  fun f ->
  (module struct
    type t = a

    let (<) b1 b2 = match f b1 b2 with
      | Lower -> true
      | LowerOrEqual | Equal | Greater | GreaterOrEqual | Uncomparable -> false

    let (<=) b1 b2 = match f b1 b2 with
      | Lower | Equal | LowerOrEqual -> true
      | Greater | GreaterOrEqual | Uncomparable -> false

    let (>) b1 b2 = match f b1 b2 with
      | Greater -> true
      | Equal | LowerOrEqual | Lower | GreaterOrEqual | Uncomparable -> false

    let (>=) b1 b2 = match f b1 b2 with
      | Greater | GreaterOrEqual | Equal -> true
      | Lower | LowerOrEqual | Uncomparable -> false

    let (===) b1 b2 = match f b1 b2 with
      | Equal -> true
      | GreaterOrEqual | Greater | Lower | LowerOrEqual | Uncomparable -> false
  end)


(* ------------------------------------------------------------------------ *)
(* --- Bounds of the segmentation                                       --- *)
(* ------------------------------------------------------------------------ *)

module Bound =
struct
  open Top.Operators
  module Var = Cil_datatype.Varinfo
  module Exp =
  struct
    include Cil_datatype.ExpStructEq
    let equal e1 e2 =
      if e1 == e2 then true else equal e1 e2
  end

  type t =
    | Const of Integer.t
    | Exp of Cil_types.exp * Integer.t (* x + c *)
    | Ptroffset of Cil_types.exp * Cil_types.offset * Integer.t (* (x - &b.offset) + c *)

  let pretty fmt : t -> unit = function
    | Const i -> Integer.pretty fmt i
    | Exp (e,i) when Integer.is_zero i -> Exp.pretty fmt e
    | Exp (e,i) when Integer.(lt i zero) ->
      Format.fprintf fmt "%a - %a" Exp.pretty e Integer.pretty (Integer.neg i)
    | Exp (e,i) ->
      Format.fprintf fmt "%a + %a" Exp.pretty e Integer.pretty i
    | _ -> raise Not_implemented

  let hash : t -> int = function
    | Const i -> Hashtbl.hash (1, Integer.hash i)
    | Exp (e, i) -> Hashtbl.hash (2, Exp.hash e, Integer.hash i)
    | Ptroffset _ -> raise Not_implemented

  let compare (b1 : t) (b2 : t) : int =
    match b1, b2 with
    | Const i1, Const i2 -> Integer.compare i1 i2
    | Exp (e1, i1), Exp (e2, i2) ->
      Exp.compare e1 e2 <?> lazy (Integer.compare i1 i2)
    | Ptroffset _, Ptroffset _ -> raise Not_implemented
    | Const _, _ -> 1
    | _, Const _-> -1
    | Exp _, _ -> 1
    | _, Exp _ -> -1

  let equal (b1 : t) (b2 : t) : bool =
    match b1, b2 with
    | Const i1, Const i2 -> Integer.equal i1 i2
    | Exp (e1, i1), Exp (e2, i2) ->
      Exp.equal e1 e2 && Integer.equal i1 i2
    | Ptroffset _, Ptroffset _ -> raise Not_implemented
    | _, _ -> false

  let of_integer (i : Integer.t) : t =
    Const i

  exception UnsupportedBoundExpression
  exception NonLinear

  (* Find a coefficient before vi in exp *)
  let rec linearity vi exp =
    match exp.Cil_types.enode with
    | Const _
    | SizeOf _ | SizeOfE _ | SizeOfStr _ | AlignOf _ | AlignOfE _
    | AddrOf _ | StartOf _ -> Integer.zero
    | Lval (Var vi', NoOffset) ->
      if Var.equal  vi' vi
      then Integer.one
      else Integer.zero
    | Lval _ -> raise UnsupportedBoundExpression
    | UnOp (Neg, e, _typ) ->
      Integer.neg (linearity vi e)
    | UnOp (_, e, _typ) | CastE (_typ, e) ->
      if Integer.is_zero (linearity vi e)
      then Integer.zero
      else raise NonLinear
    | BinOp (op, e1, e2, _typ) ->
      let l1 = linearity vi e1 and l2 = linearity vi e2 in
      match op with
      | PlusA|PlusPI -> Integer.add l1 l2
      | MinusA|MinusPI -> Integer.sub l1 l2
      | _ ->
        if Integer.(is_zero l1 && is_zero l2)
        then Integer.zero
        else raise NonLinear

  let check_support exp =
    (* Check that the linearity of any variable is not hidden into a mem access *)
    ignore (linearity Var.dummy exp)

  let of_exp exp =
    check_support exp;
    (* Normalizes x + c, c + x and x - c *)
    match Cil.constFoldToInt exp with
    | Some i -> Const i
    | None ->
      match exp.Cil_types.enode with
      | BinOp ((PlusA|PlusPI), e1, e2, _typ) ->
        begin match Cil.constFoldToInt e1, Cil.constFoldToInt e2 with
          | None, Some i -> Exp (e1, i)
          | Some i, None -> Exp (e2, i)
          | _ -> Exp (exp, Integer.zero)
        end
      | BinOp ((MinusA|MinusPI), e1, e2, _typ) ->
        begin match Cil.constFoldToInt e2 with
          | Some i -> Exp (e1, Integer.neg i)
          | None -> Exp (exp, Integer.zero)
        end
      | _ -> Exp (exp, Integer.zero)

  let _of_ptr ~base_offset e =
    (* TODO: verify type compatibility between e and base_offset *)
    match of_exp e with
    | Exp (e, c) -> Ptroffset (e, base_offset, c)
    | Const _ -> assert false (* should not happen ? even with absolute adresses ? *)
    | Ptroffset _ -> assert false (* Not produced by of_exp *)

  (* Convert bound to interval using oracle *)
  let to_int_val ~oracle = function
    | Const i -> Int_val.inject_singleton i
    | Exp (e, i) -> Int_val.add_singleton i (oracle e)
    | Ptroffset _ -> raise Not_implemented

  let to_integer ~oracle = function
    | Const i -> Some i
    | Exp (e, i) ->
      begin try
          Some (Integer.add (Int_val.project_int (oracle e)) i)
        with Ival.Not_Singleton_Int ->
          None
      end
    | Ptroffset _ -> raise Not_implemented

  let succ = function
    | Const i -> Const (Integer.succ i)
    | Exp (e, i) -> Exp (e, Integer.succ i)
    | Ptroffset _ -> raise Not_implemented

  let pred = function
    | Const i -> Const (Integer.pred i)
    | Exp (e, i) -> Exp (e, Integer.pred i)
    | Ptroffset _ -> raise Not_implemented

  let incr vi i b =
    try
      match b with
      | Const _ -> Some b
      | Exp (e, j) ->
        let l = linearity vi e in
        if Integer.is_zero l
        then Some b
        else i |> Option.map (fun i -> Exp (e, Integer.(sub j (mul l i))))
      | Ptroffset (e, base, j) ->
        let l = linearity vi e in
        if Integer.is_zero l
        then Some b
        else
          i |> Option.map (fun i ->
              Ptroffset (e, base, Integer.(sub j (mul l i))))
    with NonLinear -> None

  let incr_or_constantify ~oracle vi i b =
    match incr vi i b with
    | Some v -> Some v
    | None -> Option.map (fun c -> Const c) (to_integer ~oracle b)

  let cmp_int i1 i2 =
    let r = Integer.sub i1 i2 in
    if Integer.is_zero r
    then Equal
    else if Integer.(lt r zero) then Lower else Greater

  let cmp ~oracle b1 b2 =
    if b1 == b2
    then Equal
    else
      match b1, b2 with
      | Const i1, Const i2 -> cmp_int i1 i2
      | Exp (e1, i1), Exp (e2, i2) when Exp.equal e1 e2 -> cmp_int i1 i2
      | Ptroffset _, _ | _, Ptroffset _ -> raise Not_implemented
      | _, _ ->
        let i1 = to_int_val ~oracle b1 and i2 = to_int_val ~oracle b2 in
        let r = Int_val.(add i1 (neg i2)) in
        match Int_val.min_and_max r with
        | Some min, Some max when Integer.is_zero min && Integer.is_zero max ->
          Equal
        | Some l, _ when Integer.(ge l zero) ->
          if Integer.(gt l zero) then Greater else GreaterOrEqual
        | _, Some u when Integer.(le u zero) ->
          if Integer.(lt u zero) then Lower else LowerOrEqual
        | _ -> Uncomparable

  let eq ?(oracle=no_oracle) b1 b2 =
    cmp ~oracle b1 b2 = Equal

  let lower_integer ~oracle b =
    match Int_val.min_int (to_int_val ~oracle b) with
    | Some l -> `Value l
    | None ->
      Self.warning ~current:true "cannot retrieve a lower bound for %a"
        pretty b;
      `Top

  let upper_integer ~oracle b =
    match Int_val.max_int (to_int_val ~oracle b) with
    | Some u -> `Value u
    | None ->
      Self.warning ~current:true "cannot retrieve an upper bound for %a"
        pretty b;
      `Top

  let lower_bound ~oracle b1 b2 =
    if b1 == b2 || eq b1 b2 then `Value b1 else
      let+ i1,i2 = Top.zip
          (lower_integer ~oracle:(oracle Left) b1)
          (lower_integer ~oracle:(oracle Right) b2) in
      Const (Integer.min i1 i2)

  let upper_bound ~oracle b1 b2 =
    if b1 == b2 || eq b1 b2 then `Value b1 else
      let+ i1,i2 = Top.zip
          (upper_integer ~oracle:(oracle Left) b1)
          (upper_integer ~oracle:(oracle Right) b2) in
      Const (Integer.max i1 i2)

  let lower_const ~oracle b =
    lower_integer ~oracle b >>-: of_integer

  let upper_const ~oracle b =
    upper_integer ~oracle b >>-: of_integer

  let equivalent_bounds ~oracle b =
    match b with
    | Const _ -> [b]
    | Exp _ ->
      b :: (
        to_integer ~oracle b |>
        Option.map of_integer |>
        Option.to_list)
    | Ptroffset _ -> raise Not_implemented
end

module AgingBound =
struct
  open Top.Operators

  type age = int (* -1 means everlasting bound *)
  type t = Bound.t * age

  let debug_mode = false
  let pretty fmt (b,a) =
    if debug_mode
    then Format.fprintf fmt "%a@%d" Bound.pretty b a
    else Bound.pretty fmt b
  let hash (b,_a) = Bound.hash b
  let compare (b1,_a1) (b2,_a2) =
    Bound.compare b1 b2
  let equal_regardless_age (b1,_a1) (b2,_a2) =
    Bound.equal b1 b2
  let equal = equal_regardless_age
  let pred (b,a) = (Bound.pred b, a)
  let incr_or_constantify ~oracle vi i (b,a) =
    Bound.incr_or_constantify ~oracle vi i b |> Option.map (fun b -> b,a)
  let cmp ~oracle (b1,_a1) (b2,_a2) = Bound.cmp ~oracle b1 b2
  let eq ?oracle (b1,_a1) (b2,_a2) = Bound.eq ?oracle b1 b2
  let lower_bound ~oracle (b1,a1) (b2,a2) =
    let+ b = Bound.lower_bound ~oracle b1 b2 in
    b, min a1 a2
  let upper_bound ~oracle (b1,a1) (b2,a2) =
    let+ b = Bound.upper_bound ~oracle b1 b2 in
    b, min a1 a2
  let lower_const ~oracle (b,_a) = Bound.lower_const ~oracle b
  let upper_const ~oracle (b,_a) = Bound.upper_const ~oracle b
  let equivalent_bounds ~oracle (b,a) =
    List.map (fun b -> (b,a)) (Bound.equivalent_bounds ~oracle b)
  let birth b = b, 0
  let everlasting b = b, -1
  let is_everlasting (_b,a) = a < 0
  let aging (b,a) = b, if a >= 0 then a+1 else a
  let age (_,a) = a
  let unify_age ~other:(_,a') (b,a) = (b, min a' a)
  let operators oracle : (module Operators with type t = t) =
    operators (cmp ~oracle)
end


(* ------------------------------------------------------------------------ *)
(* --- Segmentation                                                     --- *)
(* ------------------------------------------------------------------------ *)

module type Config =
sig
  val slice_limit : unit -> int
end

module type Segmentation =
sig
  type bound = Bound.t
  type submemory
  type t
  val pretty : Format.formatter -> t -> unit
  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hull : oracle:oracle -> t -> (bound * bound) or_top
  val raw : t -> Bit.t
  val weak_erase : Bit.t -> t -> t
  val is_included : t -> t -> bool
  val unify : oracle:bioracle -> (submemory -> submemory -> submemory) ->
    t -> t -> t or_top
  val single : bit -> bound -> bound -> submemory -> t
  val read : oracle:oracle ->
    (submemory -> 'a) -> ('a -> 'a -> 'a) -> t -> bound -> bound -> 'a
  val update : oracle:oracle -> (submemory -> submemory or_bottom) ->
    t -> bound -> bound -> t or_top_bottom
  val incr_bound :
    oracle:oracle -> Cil_types.varinfo -> Integer.t option -> t -> t or_top
  val map : (submemory -> submemory) -> t -> t
  val fold : (submemory -> 'a -> 'a) -> (bit -> 'b -> 'a) -> t -> 'b -> 'a
  val add_segmentation_bounds : oracle:oracle -> bound list -> t -> t
end


module Make (Config : Config) (M : ProtoMemory) =
struct
  module B = AgingBound

  type bound = Bound.t
  type submemory = M.t

  type t = {
    start: B.t;
    segments: (M.t * B.t) list; (* should not be empty *)
    padding: bit; (* padding at the left and right of the segmentation *)
  }

  type segments = (M.t * B.t) list

  let _pretty_debug fmt (l,s) : unit =
    Format.fprintf fmt " {%a} " B.pretty l;
    let pp fmt (v,u) =
      Format.fprintf fmt "%a {%a} " M.pretty v B.pretty u
    in
    List.iter (pp fmt) s

  let pretty_segments fmt ((l : B.t), (s : (M.t * B.t) list)) : unit =
    let pp fmt (l,v,u) =
      let u = B.pred u in (* Upper bound is not included *)
      (* Less strict than B.equal even with no oracles *)
      if B.eq l u then
        Format.fprintf fmt "[%a]%a" B.pretty l M.pretty v
      else
        Format.fprintf fmt "[%a .. %a]%a" B.pretty l B.pretty u M.pretty v
    in
    match s with
    | [] -> Format.fprintf fmt "[]" (* should not happen *)
    | [(v,u)] -> pp fmt (l,v,u)
    | _ :: _ ->
      let iter l f segments =
        (* fold the previous upper bound = the current lower bound *)
        ignore (List.fold_left (fun l (v,u) -> f (l,v,u) ; u) l segments)
      in
      Pretty_memory.pp_iter (iter l) pp fmt s

  let pretty fmt (m : t) : unit =
    pretty_segments fmt (m.start,m.segments)

  let hash (m : t) : int =
    Hashtbl.hash (
      B.hash m.start,
      List.map (fun (v,u) -> Hashtbl.hash (M.hash v, B.hash u)) m.segments,
      Bit.hash m.padding)

  let compare (m1 : t) (m2 : t) : int =
    let compare_segments (v1,u1) (v2,u2) =
      M.compare v1 v2 <?> lazy (B.compare u1 u2)
    in
    B.compare m1.start m2.start <?>
    lazy (Transitioning.List.compare compare_segments m1.segments m2.segments) <?>
    lazy (Bit.compare m1.padding m2.padding)

  let equal (m1 : t) (m2 : t) : bool =
    let equal_segments (v1,u1) (v2,u2) =
      M.equal v1 v2 && B.equal u1 u2
    in
    B.equal m1.start m2.start &&
    Transitioning.List.equal equal_segments m1.segments m2.segments &&
    Bit.equal m1.padding m2.padding

  let raw (m : t) : bit =
    (* Perhaps some segments are empty, but we are not going to test it for now *)
    List.fold_left
      (fun acc (v,_u) -> Bit.join acc (M.raw v))
      m.padding m.segments

  let weak_erase (b : bit) (m : t) : t =
    {
      m with
      segments = List.map (fun (v,u) -> M.weak_erase b v, u) m.segments ;
      padding = Bit.join b m.padding ;
    }

  let is_included (m1 : t) (m2 : t) : bool =
    let included_segments (v1,u1) (v2,u2) =
      M.is_included v1 v2 && B.eq u1 u2
    in
    B.eq m1.start m2.start &&
    Bit.is_included m1.padding m2.padding &&
    try
      List.for_all2 included_segments m1.segments m2.segments
    with Invalid_argument _ -> false (* Segmentations have different sizes *)

  let rec last_bound = function
    | [] -> assert false
    | [(_v,u)] -> u
    | _ :: t -> last_bound t

  let hull ~oracle (m : t) : (bound * bound) or_top =
    let l = m.start and u = last_bound m.segments in
    Top.zip (B.lower_const ~oracle l) (B.upper_const ~oracle u)

  let is_empty_segment ~oracle l u =
    let open (val (B.operators oracle)) in
    l >= u

  let check m = (* temporarily checks type invariant; TODO: remove *)
    match m.segments with
    | [] -> assert false
    | _ :: _  -> m

  (* Segmentation normalization *)
  let remove_empty_segments ~oracle m =
    let unify_head_age (b' : B.t) : segments -> segments = function
      | [] -> [] (* Start of segmentation, age is 0, do nothing *)
      | (v,b) :: t -> (v, B.unify_age ~other:b' b) :: t
    in
    let rec aux l acc = function
      | [] -> List.rev acc
      | (v,u) :: t ->
        if B.eq ~oracle l u then (* empty segment, remove v *)
          aux l (unify_head_age u acc) t
        else
          aux u ((v,u) :: acc) t
    in
    check { m with segments = aux m.start [] m.segments }

  (* Merge the two first slices of a segmentation *)
  exception NothingToMerge
  let smash_head ~oracle l = function
    | [] | [_] -> raise NothingToMerge
    | (v1,m) :: (v2,u) :: tail ->
      let v1' = if is_empty_segment ~oracle l m then `Bottom else `Value v1
      and v2' = if is_empty_segment ~oracle m u then `Bottom else `Value v2
      in
      match Bottom.join (M.smash ~oracle) v1' v2' with
      | `Bottom -> tail
      | `Value v -> (v,u) :: tail

  let rec smash_all ~oracle l = function
    | [] -> `Bottom, l
    | [(v,u)] -> `Value v, u
    | t -> smash_all ~oracle l (smash_head ~oracle l t)


  (* Unify two arrays m1 and m2 *)
  let unify ~oracle f (m1 (*Left*): t) (m2 (*Right*) : t) : t or_top =
    let open Top.Operators in
    (* Shortcuts *)
    let left = oracle Left and right = oracle Right in
    let equals side b1 b2 = B.cmp ~oracle:(oracle side) b1 b2 = Equal in
    let smash side = Bottom.join (M.smash ~oracle:(oracle side)) in
    (* Normalise *)
    let m1 = remove_empty_segments ~oracle:left m1 in
    let m2 = remove_empty_segments ~oracle:right m2 in
    let {start=l1 ; segments=s1 ; padding=p1 } = m1
    and {start=l2 ; segments=s2 ; padding=p2 } = m2 in
    (* Unify the segmentation start *)
    let* start = B.lower_bound ~oracle l1 l2 in
    let s1 = if equals Left start l1 then s1 else (M.of_raw p1, l1) :: s1
    and s2 = if equals Right start l2 then s2 else (M.of_raw p2, l2) :: s2 in
    (* Unify the segmentation end *)
    let merge_first side = smash_head ~oracle:(oracle side) in
    let unify_end l s1 s2 acc =
      let v1, u1 = smash_all ~oracle:left l s1
      and v2, u2 = smash_all ~oracle:right l s2 in
      let+ u = B.upper_bound ~oracle u1 u2 in
      let w1 =
        if equals Left u u1 then v1 else smash Left (`Value (M.of_raw p1)) v1
      and w2 =
        if equals Right u u2 then v2 else smash Right (`Value (M.of_raw p2)) v2
      in
      match Bottom.join f w1 w2 with
      | `Bottom -> acc (* should not happen, but acc is still correct *)
      | `Value w -> ((w,u) :: acc)
    in
    (* +----+-------+-----
       | v1 | v1'   |
       +----+-------+-----
       l    u1
       +------+-------+---
       | v2   | v2'   |
       +------+-------+---
       l      u2 *)
    let rec aux l s1 s2 acc =
      (* Look for emerging slices *)
      let left_slice_emerges = match s1 with
        | (v1,u1) :: t1 ->
          begin
            try
              let candidates = B.equivalent_bounds ~oracle:left u1 in
              let u = List.find (equals Right l) candidates in
              Some (v1,u,t1)
            with Not_found -> None
          end
        | _ -> None
      and right_slice_emerges = match s2 with
        | (v2,u2) :: t2 ->
          begin
            try
              let candidates = B.equivalent_bounds ~oracle:right u2 in
              let u = List.find (equals Left l) candidates in
              Some (v2,u,t2)
            with Not_found -> None
          end
        | _ -> None
      in
      match left_slice_emerges, right_slice_emerges with
      | Some (v1,u1,t1), None -> (* left slice emerges *)
        if equals Left l u1 then (* actually empty both sides*)
          aux l t1 s2 acc
        else
          aux u1 t1 s2 ((v1,u1) :: acc)
      | None, Some (v2,u2,t2) -> (* right slice emerges *)
        if equals Right l u2 then (* actually empty both sides *)
          aux l s1 t2 acc
        else
          aux u2 s1 t2 ((v2,u2) :: acc)
      | Some _, Some _ (* both emerges, can't choose *)
      | None, None -> (* none emerges *)
        match s1, s2 with (* Are we done yet ? *)
        | [], [] -> `Value acc
        | _ :: _, [] | [], _ :: _-> unify_end l s1 s2 acc
        | (v1,u1) :: t1, (v2,u2) :: t2 ->
          try
            match B.cmp ~oracle:left u1 u2, B.cmp ~oracle:right u1 u2 with (* Compare bounds *)
            | _, Equal ->
              (* u1 and u2 can be indeferently used right side
                 -> use u1 as next bound
                 Note: Asymetric choice, u2 may also be a good choice *)
              aux u1 t1 t2 ((f v1 v2, u1) :: acc)
            | Equal, _ ->
              (* u1 and u2 can be indeferently used left side
                 -> use u2 as next bound *)
              aux u2 t1 t2 ((f v1 v2, u2) :: acc)
            | _, _ when B.is_everlasting u1 && not (B.is_everlasting u2) ->
              (* Remove the right bound to keep the left everlasting bound *)
              aux l s1 (merge_first Right l s2) acc
            | _, _ when B.is_everlasting u2 && not (B.is_everlasting u1) ->
              (* Remove the left bound to keep the right everlasting bound *)
              aux l (merge_first Left l s1) s2 acc
            | (Greater | GreaterOrEqual),
              (Greater | GreaterOrEqual | Uncomparable) ->
              (* u1 >= u2 on the left side, we are sure u2 doesn't appear left
                 -> remove u2, merge slices *)
              aux l s1 (merge_first Right l s2) acc
            | (Lower | LowerOrEqual | Uncomparable),
              (Lower | LowerOrEqual) ->
              (* u1 <= u2 on the right side, we are sure u1 doesn't appear right
                 -> remove u1, merge slices *)
              aux l (merge_first Left l s1) s2 acc
            | (Greater | GreaterOrEqual), (Lower | LowerOrEqual) (* Can't choose which bound to remove first *)
            | (Lower | LowerOrEqual | Uncomparable),
              (Greater | GreaterOrEqual | Uncomparable) ->
              aux l (merge_first Left l s1) (merge_first Right l s2) acc
          with NothingToMerge -> (* There is nothing left to merge *)
            unify_end l s1 s2 acc
    in
    let+ rev_segments = aux start s1 s2 [] in
    let segments = List.rev rev_segments in
    (* Iterate through segmentations *)
    check { start ; segments ; padding = Bit.join p1 p2 }

  let single padding lindex (* included *) uindex (* excluded *) value =
    check {
      padding ;
      start = B.birth lindex ;
      segments = [(value,B.birth uindex)] ;
    }

  let read ~oracle map reduce m lindex uindex =
    let open (val (B.operators oracle)) in
    let lindex = B.birth lindex and uindex = B.birth uindex in
    let fold acc x =
      Bottom.join reduce acc (`Value (map x))
    in
    let aux (l,acc) (v,u) =
      u, if l > uindex || u <= lindex then acc else fold acc v
    in
    let acc = `Bottom in
    let acc = if m.start <= lindex then acc else fold acc (M.of_raw m.padding) in
    let last,acc = List.fold_left aux (m.start,acc) m.segments in
    let acc = if last > uindex then acc else fold acc (M.of_raw m.padding) in
    match acc with
    | `Bottom -> assert false (* TODO: ensure that with typing *)
    | `Value v -> v

  let aging m = (* Extremities do not age *)
    let rec aux acc = function
      | [] -> acc
      | [x] -> x :: acc
      | (v,b) :: t -> aux ((v,B.aging b) :: acc) t
    in
    { m with segments = List.rev (aux [] m.segments) }

  let age m = (* Age of the segmentation / age of the oldest bound *)
    match m.segments with (* ignore m.start bound *)
    | [] -> None
    | (_,b) :: t ->
      let rec aux acc = function
        | [] -> None
        | [_] -> Some acc (* ignore last bound *)
        | (_,b) :: t -> aux (max acc (B.age b)) t
      in
      aux (B.age b) t

  (* Remove all bounds >= limit *)
  let remove_elderlies ~oracle limit m =
    let rec aux acc l = function
      | ([] | [_]) as t -> List.rev (t @ acc)
      | ((v,u) :: t) as s ->
        if B.age u >= limit then
          aux acc l (smash_head ~oracle l s)
        else
          aux ((v,u) :: acc) u t
    in
    { m with segments = aux [] m.start m.segments }

  let limit_size ~oracle m =
    let limit = max 1 (Config.slice_limit ()) in
    let rec aux m =
      if List.length m.segments <= limit
      then m
      else
        match age m with
        | None -> m (* no inner bounds, should not happen if segments_limit > 2 *)
        | Some oldest when oldest > 0 -> aux (remove_elderlies ~oracle oldest m)
        | Some _ -> m
    in
    aux m

  (* TODO: partitioning strategies
     1. reinforcement without loss
     2. weak update without singularization
     3. update reduces the number of segments to 3 *)
  let update ~oracle f m lindex (* included *) uindex (* excluded *) = (* lindex < uindex *)
    let open TopBottom.Operators in
    let open (val (B.operators oracle)) in
    let same_bounds = lindex == uindex in (* happens when adding partitioning hints *)
    let lindex, uindex =
      if same_bounds
      then B.everlasting lindex, B.everlasting uindex
      else B.birth lindex, B.birth uindex in
    (* (start,head) : segmentation kept identical below the update indexes,
                      head is a list in reverse order
       (l,v,u) : the segment (l,u) beeing overwriten with previous value v

       head = (_,l) :: _
    *)
    let rec aux_before l s =
      if lindex >= l
      then aux_below l [] l s
      else
        let* l = B.lower_bound ~oracle:(fun _ -> oracle) lindex l in
        aux_over l [] l (M.of_raw m.padding) l s
    and aux_below start head l = fun t ->
      match t with (* l <= lindex *)
      | [] ->
        aux_end start head l (M.of_raw m.padding) uindex []
      | (v,u) :: t ->
        if lindex >= u
        then aux_below start ((v,u) :: head) u t
        else aux_over start head l v u t
    and aux_over start head l v u s = (* l <= lindex *)
      if uindex <= u then
        aux_end start head l v u s
      else
        match s with
        | [] ->
          let* u = B.upper_bound ~oracle:(fun _ -> oracle) u uindex in
          let v = M.smash ~oracle v (M.of_raw m.padding) in
          aux_end start head l v u []
        | (v',u') :: t ->
          (* TODO: do not smash for overwrites if the slices are covered by the write *)
          aux_over start head l (M.smash ~oracle v v') u' t
    and aux_end start head l v u tail = (* l <= lindex < uindex <= u*)
      let+ new_v = f v in
      let previous_is_empty = is_empty_segment ~oracle l lindex
      and next_is_empty = is_empty_segment ~oracle uindex u in
      let tail' =
        (if previous_is_empty then [] else [(v,lindex)]) @
        (if same_bounds then [] else [(new_v,uindex)]) @
        (if next_is_empty then [] else [(v,u)]) @
        tail
      and head',start' = match head with (* change last bound to match lindex *)
        | (v',_u) :: t when previous_is_empty -> (v',lindex) :: t, start
        | [] when previous_is_empty -> [], lindex
        | head -> head, start
      in
      check {
        padding = m.padding;
        segments = List.rev_append head' tail';
        start = start';
      }
    in
    let m = if same_bounds then m else remove_empty_segments ~oracle m in
    aux_before m.start m.segments >>-:
    aging >>-:
    limit_size ~oracle


  let incr_bound ~oracle vi x m =
    (* Removing empty segments must be done before updating bounds as the oracle
       is only valid before the update *)
    let m = remove_empty_segments ~oracle m in
    let incr = B.incr_or_constantify ~oracle vi x in
    let rec incr_start p l = function
      | [] -> `Top (* No more segments, top segmentation *)
      | (v,u) :: t as s ->
        match incr l with
        | Some l' -> incr_end p l' (List.rev s)
        | None -> (* No replacement, try to find a lower bound instead *)
          match B.lower_const ~oracle l with
          | `Top -> (* No lower bound, completely remove the segment *)
            let p' = Bit.join p (M.raw v) in
            incr_start p' u t
          | `Value l' ->
            let v' = M.smash ~oracle (M.of_raw p) v in
            incr_end p (B.birth l') (List.rev ((v',u) :: t))
    and incr_end p l = function (* In reverse order *)
      | [] -> `Top (* No more segments, top segmentation *)
      | (v,u) :: t ->
        match incr u with
        | Some u' -> incr_inner p l [] ((v,u') :: t)
        | None -> (* No replacement, try to find an upper bound instead *)
          match B.upper_const ~oracle u with
          | `Top -> (* No upper bound, completely remove the segment *)
            let p' = Bit.join p (M.raw v) in
            incr_end p' l t
          | `Value u' ->
            let v' = M.smash ~oracle (M.of_raw p) v in
            incr_inner p l [] ((v',B.birth u') :: t)
    and incr_inner p l acc (* In right order *) = function (* In reverse order *)
      | [] -> assert false
      | [s] ->
        `Value (check { start=l ; padding=p ; segments=s :: acc })
      | (v1,u) :: (v2,m) :: t -> (* u is already increased *)
        match incr m with
        | Some m' ->
          incr_inner p l ((v1,u) :: acc) ((v2,m') :: t)
        | None ->
          let v' = M.smash ~oracle v1 v2 in
          incr_inner p l acc ((v',u) :: t)
    in
    incr_start m.padding m.start m.segments

  let map f m =
    check { m with segments=List.map (fun (v,u) -> f v, u) m.segments }

  let fold fs fp m acc =
    List.fold_left (fun acc (v,_) -> fs v acc) (fp m.padding acc) m.segments

  let add_segmentation_bounds ~oracle bounds m =
    let add_bound m b =
      match update ~oracle (fun x -> `Value x) m b b with
      | `Value m -> m
      | `Bottom -> assert false
      | `Top ->
        Self.warning ~current:true
          "failed to introduce %a inside the array segmentation"
          Bound.pretty b;
        m
    in
    List.fold_left add_bound m bounds
end
