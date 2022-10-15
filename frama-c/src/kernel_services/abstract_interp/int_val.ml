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

let small_cardinal = Int_set.get_small_cardinal
let small_cardinal_Int () = Int.of_int (small_cardinal ())

let emitter = Lattice_messages.register "Int_val"
let log_imprecision s = Lattice_messages.emit_imprecision emitter s

module Widen_Hints = Datatype.Integer.Set
type size_widen_hint = Integer.t
type generic_widen_hint = Widen_Hints.t
type widen_hint = size_widen_hint * generic_widen_hint

(* --------------------------------- Datatype ------------------------------- *)

type int_val =
  | Set of Int_set.t
  | Itv of Int_interval.t

let top = Itv Int_interval.top

let hash = function
  | Set s -> Int_set.hash s
  | Itv i -> Int_interval.hash i

let compare e1 e2 =
  match e1, e2 with
  | Set s1, Set s2 -> Int_set.compare s1 s2
  | Itv i1, Itv i2 -> Int_interval.compare i1 i2
  | _, Set _ -> 1
  | Set _, _ -> -1

let equal e1 e2 = compare e1 e2 = 0

let pretty fmt = function
  | Itv i -> Int_interval.pretty fmt i
  | Set s -> Int_set.pretty fmt s

include Datatype.Make_with_collections
    (struct
      type t = int_val
      let name = "int_val"
      open Structural_descr
      let structural_descr =
        t_sum
          [| [| Int_set.packed_descr |];
             [| Int_interval.packed_descr |] |]
      let reprs = [ top ]
      let equal = equal
      let compare = compare
      let hash = hash
      let pretty = pretty
      let rehash x = x
      let internal_pretty_code = Datatype.pp_fail
      let mem_project = Datatype.never_any_project
      let copy = Datatype.undefined
      let varname = Datatype.undefined
    end)

(* ------------------------------- Constructors ----------------------------  *)

let zero = Set Int_set.zero
let one = Set Int_set.one
let minus_one = Set Int_set.minus_one
let zero_or_one = Set Int_set.zero_or_one

let positive_integers = Itv (Int_interval.inject_range (Some Int.zero) None)
let negative_integers = Itv (Int_interval.inject_range None (Some Int.zero))

let inject_singleton e = Set (Int_set.inject_singleton e)

let make ~min ~max ~rem ~modu =
  match min, max with
  | Some mn, Some mx ->
    assert (Int.le mn mx);
    if Int.equal mx mn
    then inject_singleton mn
    else
      let l = Int.succ (Int.e_div (Int.sub mx mn) modu) in
      if Int.le l (small_cardinal_Int ())
      then Set (Int_set.inject_periodic ~from:mn ~period:modu ~number:l)
      else Itv (Int_interval.make ~min ~max ~rem ~modu)
  | _ -> Itv (Int_interval.make ~min ~max ~rem ~modu)

let check_make ~min ~max ~rem ~modu =
  Int_interval.check ~min ~max ~rem ~modu;
  make ~min ~max ~rem ~modu

let inject_interval ~min ~max ~rem:r ~modu =
  assert ((Int.ge r Int.zero ) && (Int.ge modu Int.one) && (Int.lt r modu));
  let fix_bound fix bound = match bound with
    | None -> None
    | Some b -> Some (if Int.equal b (Int.e_rem r modu) then b else fix b)
  in
  let min = fix_bound (fun min -> Int.round_up_to_r ~min ~r ~modu) min
  and max = fix_bound (fun max -> Int.round_down_to_r ~max ~r ~modu) max in
  make ~min ~max ~rem:r ~modu

let inject_range min max = make ~min ~max ~rem:Int.zero ~modu:Int.one

let check_make_or_bottom ~min ~max ~rem ~modu =
  match min, max with
  | Some mn, Some mx when Int.gt mn mx -> `Bottom
  | _, _ -> `Value (check_make ~min ~max ~rem ~modu)

(* ------------------------- Sets and Intervals ---------------------------- *)

(* If an interval represents less than [small_cardinal_Int] integers, then
   converts the interval into a set. Used for the return of Int_interval
   functions that may reduce intervals.*)
let inject_itv i =
  match Int_interval.cardinal i with
  | None -> Itv i
  | Some card ->
    if Int.le card (small_cardinal_Int ())
    then
      let min, max, rem, modu = Int_interval.min_max_rem_modu i in
      make ~min ~max ~rem ~modu
    else Itv i

let inject_set s = Set s

(* Int_set functions that enlarge sets returns either a small integer set,
   or an interval as `Top (min, max, modu). The following functions inject
   these results as proper integer abstractions of type t.*)

let inject_pre_itv ~min ~max ~modu =
  let rem = Int.e_rem min modu in
  Itv (Int_interval.make ~min:(Some min) ~max:(Some max) ~rem ~modu)

let inject_set_or_top = function
  | `Set s -> Set s
  | `Top (min, max, modu) -> inject_pre_itv ~min ~max ~modu

let inject_set_or_top_or_bottom = function
  | `Bottom -> `Bottom
  | `Set s -> `Value (Set s)
  | `Top (min, max, modu) -> `Value (inject_pre_itv ~min ~max ~modu)

(* Computes [min], [max], [rem] and [modu] from an integer set. *)
let make_top_from_set s =
  let min = Int_set.min s in
  let rem, modu =
    if Int_set.cardinal s = 1
    then Int.zero, min
    else
      let modu =
        Int_set.fold (fun x acc -> Int.pgcd (Int.sub x min) acc) s Int.zero
      in
      Int.e_rem min modu, modu
  in
  let max = Some (Int_set.max s) in
  let min = Some min in
  min, max, rem, modu

(* Converts an integer set into an interval, regardless of the set cardinal.
   Useful for functions not implemented (or irrelevant) in Int_set. *)
let make_itv_from_set s =
  let min, max, rem, modu = make_top_from_set s in
  Int_interval.make ~min ~max ~rem ~modu

let make_itv = function
  | Itv i -> i
  | Set s -> make_itv_from_set s

let make_range = function
  | Itv i -> i
  | Set s ->
    let min, max = Int_set.min s, Int_set.max s in
    Int_interval.inject_range (Some min) (Some max)

(* -------------------------------- Utils ----------------------------------- *)

let min_le_elt min elt =
  match min with
  | None -> true
  | Some m -> Int.le m elt

let max_ge_elt max elt =
  match max with
  | None -> true
  | Some m -> Int.ge m elt

let is_zero x = equal x zero
let is_one = equal one

let contains_zero = function
  | Itv i -> Int_interval.mem Int.zero i
  | Set s -> Int_set.mem Int.zero s

let contains_non_zero = function
  | Itv _ -> true (* at least two values *)
  | Set _ as s -> not (is_zero s)

let fold_int ?(increasing=true) f v acc =
  match v with
  | Itv i -> Int_interval.fold_int ~increasing f i acc
  | Set s -> Int_set.fold ~increasing f s acc

let fold_enum f v acc = fold_int (fun x acc -> f (inject_singleton x) acc) v acc

(* -------------------------------- Accessors ------------------------------- *)

let min_int = function
  | Itv i -> fst (Int_interval.min_and_max i)
  | Set s -> Some (Int_set.min s)

let max_int = function
  | Itv i -> snd (Int_interval.min_and_max i)
  | Set s -> Some (Int_set.max s)

let min_and_max = function
  | Set s -> Some (Int_set.min s), Some (Int_set.max s)
  | Itv i -> Int_interval.min_and_max i

let min_max_rem_modu = function
  | Set s -> make_top_from_set s
  | Itv i -> Int_interval.min_max_rem_modu i

exception Not_Singleton
let project_int = function
  | Set s ->
    if Int_set.cardinal s = 1 then Int_set.min s else raise Not_Singleton
  | Itv _ -> raise Not_Singleton

let is_small_set = function
  | Set _ -> true
  | Itv _ -> false

let project_small_set = function
  | Set a -> Some (Int_set.to_list a)
  | Itv _ -> None

(* ----------------------------- Cardinality -------------------------------- *)

let is_singleton = function
  | Itv _ -> false
  | Set s -> Int_set.cardinal s = 1

let cardinal_zero_or_one = function
  | Set s -> Int_set.cardinal s <= 1
  | Itv _ -> false

let cardinal = function
  | Set s -> Some (Int.of_int (Int_set.cardinal s))
  | Itv i -> Int_interval.cardinal i

let cardinal_estimate ~size = function
  | Set s -> Int.of_int (Int_set.cardinal s)
  | Itv i -> Option.value ~default:(Int.two_power size) (Int_interval.cardinal i)

let cardinal_less_than v n =
  let c =
    match v with
    | Set s -> Int.of_int (Int_set.cardinal s)
    | Itv i -> Extlib.the ~exn:Not_less_than (Int_interval.cardinal i)
  in
  if Int.le c (Int.of_int n)
  then Int.to_int_exn c (* This is smaller than the original [n] *)
  else raise Not_less_than

let cardinal_is_less_than v n =
  match cardinal v with
  | None -> false
  | Some c -> Int.le c (Int.of_int n)

let diff_if_one value rem =
  match rem with
  | Set s when Int_set.cardinal s = 1 ->
    begin
      let v = Int_set.min s in
      match value with
      | Set s -> Int_set.remove s v >>-: fun s -> Set s
      | Itv i ->
        let min, max, rem, modu = Int_interval.min_max_rem_modu i in
        match min, max with
        | Some mn, _ when Int.equal v mn ->
          check_make_or_bottom ~min:(Some (Int.add mn modu)) ~max ~rem ~modu
        | _, Some mx when Int.equal v mx ->
          check_make_or_bottom ~min ~max:(Some (Int.sub mx modu)) ~rem ~modu
        | Some mn, Some mx when
            Int.equal (Int.sub mx mn) (Int.mul modu (small_cardinal_Int ()))
            && Int_interval.mem v i ->
          let list =
            Int_interval.fold_int
              (fun i acc -> if Int.equal i v then acc else i :: acc)
              i []
          in
          `Value (Set (Int_set.inject_list list))
        | _, _ -> `Value value
    end
  | _ -> `Value value

let diff value rem =
  log_imprecision "Ival.diff";
  diff_if_one value rem

(* ------------------------------- Lattice ---------------------------------- *)

let is_included t1 t2 =
  match t1, t2 with
  | Itv i1, Itv i2 -> Int_interval.is_included i1 i2
  | Set s1, Set s2 -> Int_set.is_included s1 s2
  | Itv _, Set _ -> false (* Itv _ represents more elements
                             than can be represented by Set _ *)
  | Set s, Itv i ->
    let min, max, rem, modu = Int_interval.min_max_rem_modu i in
    (* Inclusion of bounds is needed for the entire inclusion *)
    min_le_elt min (Int_set.min s) && max_ge_elt max (Int_set.max s)
    && (Int.equal Int.one modu (* Top side contains all integers, we're done *)
        || Int_set.for_all (fun x -> Int.equal (Int.e_rem x modu) rem) s)

let join v1 v2 =
  match v1, v2 with
  | Itv i1, Itv i2 -> Itv (Int_interval.join i1 i2)
  | Set s1, Set s2 -> inject_set_or_top (Int_set.join s1 s2)
  | Set s, Itv i
  | Itv i, Set s ->
    let min, max, r, modu = Int_interval.min_max_rem_modu i in
    let f elt modu = Int.pgcd modu (Int.abs (Int.sub r elt)) in
    let modu = Int_set.fold f s modu in
    let rem = Int.e_rem r modu in
    let min = match min with
        None -> None
      | Some m -> Some (Int.min m (Int_set.min s))
    in
    let max = match max with
        None -> None
      | Some m -> Some (Int.max m (Int_set.max s))
    in
    Itv (Int_interval.make ~min ~max ~rem ~modu)

let link v1 v2 =
  match v1, v2 with
  | Set s1, Set s2 -> inject_set_or_top (Int_set.link s1 s2)
  | Itv i1, Itv i2 -> Itv (Int_interval.link i1 i2)
  | Itv i, Set s | Set s, Itv i ->
    let min, max, rem, modu = Int_interval.min_max_rem_modu i in
    let move_bound add = function
      | None -> None
      | Some bound ->
        let cur = ref bound in
        Int_set.iter (fun e -> if Int.equal e (add !cur modu) then cur := e) s;
        Some !cur
    in
    let min = move_bound Int.sub min
    and max = move_bound Int.add max in
    check_make ~min ~max ~rem ~modu

let meet v1 v2 =
  match v1, v2 with
  | Itv i1, Itv i2 -> Int_interval.meet i1 i2 >>-: inject_itv
  | Set s1 , Set s2 -> Int_set.meet s1 s2 >>-: inject_set
  | Set s, Itv itv
  | Itv itv, Set s ->
    Int_set.filter (fun i -> Int_interval.mem i itv) s >>-: inject_set

let narrow = meet (* meet is exact *)

let widen widen_hints t1 t2 =
  if equal t1 t2 || cardinal_zero_or_one t1 then t2
  else
    match t2 with
    | Itv _ | Set _ ->
      let i1 = make_itv t1
      and i2 = make_itv t2 in
      inject_itv (Int_interval.widen widen_hints i1 i2)

let intersects v1 v2 =
  match v1, v2 with
  | Itv _, Itv _ -> not (meet v1 v2 = `Bottom) (* YYY: slightly inefficient *)
  | Set s1 , Set s2 -> Int_set.intersects s1 s2
  | Set s, Itv itv | Itv itv, Set s ->
    Int_set.exists (fun i -> Int_interval.mem i itv) s

let complement_under ~size ~signed i =
  let max = Int.two_power_of_int (if signed then size - 1 else size) in
  let min = if signed then Int.neg max else Int.zero in
  let max = Int.pred max in
  match i with
  | Set set ->
    inject_set_or_top_or_bottom (Int_set.complement_under ~min ~max set)
  | Itv itv ->
    Int_interval.complement_under ~min ~max itv >>-: inject_itv

(* -------------------------------- Arithmetics ----------------------------- *)

let add_singleton i = function
  | Set s -> Set (Int_set.add_singleton i s)
  | Itv itv -> Itv (Int_interval.add_singleton_int i itv)

let add v1 v2 =
  match v1, v2 with
  | Set s1, Set s2 -> inject_set_or_top (Int_set.add s1 s2)
  | Itv i1, Itv i2 -> Itv (Int_interval.add i1 i2)
  | Set s, Itv i | Itv i, Set s ->
    if Int_set.cardinal s = 1
    then Itv (Int_interval.add_singleton_int (Int_set.min s) i)
    else Itv (Int_interval.add i (make_itv_from_set s))

let add_under v1 v2 =
  match v1, v2 with
  | Set s1, Set s2 -> `Value (inject_set_or_top (Int_set.add_under s1 s2))
  | Itv i1, Itv i2 -> Int_interval.add_under i1 i2 >>-: inject_itv
  | Set s, Itv i | Itv i, Set s ->
    if Int_set.cardinal s <> 1
    then log_imprecision "Ival.add_int_under";
    (* This is precise if [s] has only one element. Otherwise, this is not worse
       than another computation. *)
    `Value (Itv (Int_interval.add_singleton_int (Int_set.min s) i))

let neg = function
  | Set s -> Set (Int_set.neg s)
  | Itv i -> Itv (Int_interval.neg i)

let abs = function
  | Set s -> Set (Int_set.abs s)
  | Itv i -> inject_itv (Int_interval.abs i)


let scale f v =
  if Int.is_zero f
  then zero
  else
    match v with
    | Set s -> Set (Int_set.scale f s)
    | Itv i-> Itv (Int_interval.scale f i)

let scale_div ~pos f v =
  assert (not (Int.is_zero f));
  match v with
  | Set s -> Set (Int_set.scale_div ~pos f s)
  | Itv i -> inject_itv (Int_interval.scale_div ~pos f i)

let scale_div_or_bottom ~pos f v =
  if Int.is_zero f then `Bottom else `Value (scale_div ~pos f v)

(* TODO: a more precise result could be obtained by transforming
   Itv(min,max,r,m) into Itv(min,max,r/f,m/gcd(m,f)). But this is
   more complex to implement when pos or f is negative. *)
let scale_div_under ~pos f v =
  assert (not (Int.is_zero f));
  match v with
  | Set s -> `Value (Set (Int_set.scale_div ~pos f s))
  | Itv i -> Int_interval.scale_div_under ~pos f i >>-: inject_itv

let mul v1 v2 =
  if is_one v1 then v2
  else if is_zero v2 || is_zero v1 then zero
  else if is_one v2 then v1
  else
    match v1, v2 with
    | Set s1, Set s2 -> inject_set_or_top (Int_set.mul s1 s2)
    | Itv i1, Itv i2 -> Itv (Int_interval.mul i1 i2)
    | Set s, Itv i | Itv i, Set s ->
      if Int_set.cardinal s = 1
      then Itv (Int_interval.scale (Int_set.min s) i)
      else Itv (Int_interval.mul i (make_itv_from_set s))

let div x y =
  match y with
  | Set sy ->
    Int_set.fold
      (fun elt acc ->
         Bottom.join join acc (scale_div_or_bottom ~pos:false elt x))
      sy `Bottom
  | Itv iy -> Int_interval.div (make_range x) iy >>-: inject_itv

(* [scale_rem ~pos:false f v] is an over-approximation of the set of
   elements [x mod f] for [x] in [v].
   [scale_rem ~pos:true f v] is an over-approximation of the set of
   elements [x pos_rem f] for [x] in [v]. *)
let scale_rem ~pos f = function
  | Set s -> inject_set (Int_set.scale_rem ~pos f s)
  | Itv i -> inject_itv (Int_interval.scale_rem ~pos f i)

let scale_rem_or_bottom ~pos f v =
  if Int.is_zero f then `Bottom else `Value (scale_rem ~pos f v)

let c_rem x y =
  match y with
  | Itv iy -> Int_interval.c_rem (make_range x) iy >>-: inject_itv
  | Set yy ->
    match x with
    | Set xx -> inject_set_or_top_or_bottom (Int_set.c_rem xx yy)
    | Itv _ ->
      let f y acc =
        Bottom.join join (scale_rem_or_bottom ~pos:false y x) acc
      in
      Int_set.fold f yy `Bottom

(** Computes [x (op) ({y >= 0} * 2^n)], as an auxiliary function for
    [shift_left] and [shift_right]. [op] and [scale] must verify
    [scale a b == op (inject_singleton a) b] *)
let shift_aux scale op (x: t) (y: t) =
  narrow (inject_range (Some Int.zero) None) y >>-: fun y ->
  try
    match y with
    | Set s -> Int_set.map_reduce (fun n -> scale (Int.two_power n) x) join s
    | Itv _ ->
      let min = Option.map Int.two_power (min_int y) in
      let max = Option.map Int.two_power (max_int y) in
      let modu = match min with None -> Int.one | Some m -> m in
      let factor = check_make ~min ~max ~rem:Int.zero ~modu in
      op x factor
  with Z.Overflow ->
    Lattice_messages.emit_imprecision emitter "Ival.shift_aux";
    (* We only preserve the sign of the result *)
    if is_included x positive_integers then positive_integers
    else
    if is_included x negative_integers then negative_integers
    else top

let shift_right x y =
  let div a b = Bottom.non_bottom (div a b) in
  shift_aux (scale_div ~pos:true) div x y

let shift_left x y = shift_aux scale mul x y


(* ----------------------------------- Misc --------------------------------- *)

let create_all_values ~signed ~size =
  let min, max =
    if signed then
      let b = Int.two_power_of_int (size - 1) in
      Int.neg b, Int.pred b
    else
      let b = Int.two_power_of_int size in
      Int.zero, Int.pred b
  in
  inject_range (Some min) (Some max)

let cast_int_to_int ~size ~signed value =
  if equal top value
  then create_all_values ~size:(Int.to_int_exn size) ~signed
  else
    let result =
      match value with
      | Itv i -> inject_itv (Int_interval.cast ~size ~signed i)
      | Set s ->
        let all =
          create_all_values ~size:(Int.to_int_exn size) ~signed
        in
        if is_included value all
        then value
        else
          let rem_f value = Int.cast ~size ~signed ~value in
          Set (Int_set.map rem_f s)
    in
    (* If sharing is no longer preserved, please change Cvalue.V.cast *)
    if equal result value then value else result

let all_values ~size = function
  | Itv i ->
    begin
      let min, max, _, modu = Int_interval.min_max_rem_modu i in
      match min, max with
      | None, _ | _, None -> Int.is_one modu
      | Some mn, Some mx ->
        Int.is_one modu &&
        Int.le
          (Int.two_power size)
          (Int.length mn mx)
    end
  | Set s as v ->
    let siz = Int.to_int_exn size in
    Int_set.cardinal s >= 1 lsl siz &&
    equal
      (cast_int_to_int ~size ~signed:false v)
      (create_all_values ~size:siz ~signed:false)

let subdivide = function
  | Set s -> let s1, s2 = Int_set.subdivide s in Set s1, Set s2
  | Itv i ->
    let i1, i2 = Int_interval.subdivide i in
    let t1 = inject_itv i1
    and t2 = inject_itv i2 in
    t1, t2

let extract_bits ~start ~stop = function
  | Set s -> Set (Int_set.map (Int.extract_bits ~start ~stop) s)
  | Itv _ as d ->
    try
      let dived = scale_div ~pos:true (Int.two_power start) d in
      let factor = Int.two_power (Int.length start stop) in
      scale_rem ~pos:true factor dived
    with Z.Overflow ->
      Lattice_messages.emit_imprecision emitter "Ival.extract_bits";
      top

let make = check_make

(* ------------------------------------------------------------------------ *)
(* --- Bitwise operators                                                --- *)
(* ------------------------------------------------------------------------ *)

(* --- Bit lattice --- *)

type bit_value = On | Off | Both

module Bit =
struct
  type t = bit_value

  let to_string = function
    | Off -> "0"
    | On -> "1"
    | Both -> "T"

  let _pretty (fmt : Format.formatter) (b :t) =
    Format.pp_print_string fmt (to_string b)

  let union (b1 : t) (b2 : t) : t =
    if b1 = b2 then b1 else Both

  let not : t -> t = function
    | On -> Off
    | Off -> On
    | Both -> Both
end


(* --- Bit operators --- *)

module type BitOperator =
sig
  (* Concrete version of the bitwise operator *)
  val concrete_bitwise : Int.t -> Int.t -> Int.t
  (* Printable version of the operator *)
  val representation : string
  (* forward is given here as the lifted function of some bit operator op
     where op
     1. is assumed to be commutative (backward functions do not assume the
        position of the arguments)
     2. must ensure  0 op 0 = 0  as otherwise applying op on a sign bit may
        produce a negative result from two positive operands; but we don't
        want to produce a negative result when the operation is unsigned which
        we don't know unless one of the operands is negative;
     3. is not constant, otherwise nothing of all of this makes sense.
     forward is defined as
     forward b1 b2 = { x1 op x2 | x1 \in b1, x2 \in b2 } *)
  val forward : bit_value -> bit_value -> bit_value
  (* backward_off b = { x | \exist y \in b . x op y = y op x = 1 } *)
  val backward_off : bit_value -> bit_value
  (* backward_on b = { x | \exist y \in b . x op y = y op x = 0 } *)
  val backward_on : bit_value -> bit_value
end

module And : BitOperator =
struct
  let concrete_bitwise = Int.logand

  let representation = "&"

  let forward v1 v2 =
    match v1 with
    | Off -> Off
    | On -> v2
    | Both -> if v2 = Off then Off else Both

  let backward_off = function
    | (Off | Both) -> Both
    | On -> Off

  let backward_on = function
    | Off -> assert false
    | (On | Both) -> On
end

module Or : BitOperator =
struct
  let concrete_bitwise = Int.logor

  let representation = "|"

  let forward v1 v2 =
    match v1 with
    | On -> On
    | Off -> v2
    | Both -> if v2 = On then On else Both

  let backward_off = function
    | On -> assert false
    | (Off | Both) -> Off

  let backward_on = function
    | (On | Both) -> Both
    | Off -> On
end

module Xor : BitOperator =
struct
  let concrete_bitwise = Int.logxor

  let representation = "^"

  let forward v1 v2 =
    match v1 with
    | Both -> Both
    | Off -> v2
    | On -> Bit.not v2

  let backward_on v = Bit.not v

  let backward_off v = v
end


(* --- Bit extraction and mutation --- *)

let significant_bits (v : t) : int option =
  match min_and_max v with
  | None, _ | _, None -> None
  | Some l, Some u -> Some (max (Z.numbits l) (Z.numbits u))

let extract_sign (v : t) : bit_value =
  match min_and_max v with
  | _, Some u when Int.(lt u zero) -> On
  | Some l, _ when Int.(ge l zero) -> Off
  | _, _ -> Both

let extract_bit (i : int) (v : t) : bit_value =
  let bit_value x = if Z.testbit x i then On else Off in
  match v with
  | Set s -> Int_set.map_reduce bit_value Bit.union s
  | Itv itv ->
    match Int_interval.min_and_max itv with
    | None, _ | _, None -> Both
    | Some l, Some u ->
      (* It does not take modulo into account *)
      if Int.(ge (sub u l) (two_power_of_int i)) (* u - l >= mask *)
      then Both
      else Bit.union (bit_value l) (bit_value u)

let reduce_sign v = function
  | Both -> `Value v
  | On ->
    begin match v with
      | Set s -> Int_set.filter Int.(gt zero) s >>-: inject_set
      | Itv itv -> Int_interval.reduce_sign itv true >>-: inject_itv
    end
  | Off ->
    begin match v with
      | Set s -> Int_set.filter Int.(le zero) s >>-: inject_set
      | Itv itv -> Int_interval.reduce_sign itv false >>-: inject_itv
    end

let reduce_bit (i : int) (v : t) (b : bit_value) : t or_bottom =
  let bit_value x = if Z.testbit x i then On else Off in
  if b = Both
  then `Value v
  else match v with
    | Set s -> Int_set.filter (fun x -> bit_value x = b) s >>-: inject_set
    | Itv itv -> Int_interval.reduce_bit i itv (b = On) >>-: inject_itv

type bit = Sign | Bit of int

let extract_bit = function
  | Sign -> extract_sign
  | Bit i -> extract_bit i

let set_bit_on ~size bit =
  let mask = match bit with
    | Sign -> Int.(neg (two_power_of_int size))
    | Bit i -> Int.(two_power_of_int i)
  in
  fun v -> Int.logor mask v

let reduce_bit = function
  | Sign -> reduce_sign
  | Bit i -> reduce_bit i

(* --- Bitwise binary operators --- *)

module BitwiseOperator (Op : BitOperator) =
struct

  let backward (b : bit_value) = function
    | On -> Op.backward_on b
    | Off -> Op.backward_off b
    | Both -> assert false

  (** Bit masks are composed of an array of significant bit values where index 0
      represents the lowest bit, and a single bit_value to represent the
      possible leading bits. *)
  type bit_mask = bit_value array * bit_value

  (* Converts an integer [x] into a bit array of size [n]. *)
  let int_to_bit_array n (x : Int.t) =
    let make i = if Z.testbit x i then On else Off in
    Array.init n make

  (* Computes a bit_mask for the lowest bits of an ival, using the modulo
     information for non singleton values. *)
  let low_bit_mask : t -> bit_mask = function
    | Set s when Int_set.cardinal s = 1 -> (* singleton : build a full mask  *)
      let x = Int_set.min s in
      let n = Z.numbits x in
      int_to_bit_array n x, if Int.(ge x zero) then Off else On
    | v ->
      let _,_,r,modu = min_max_rem_modu v in (* requires cardinal > 1 *)
      (* Find how much [modu] can be divided by two. *)
      let n = Z.trailing_zeros modu in
      int_to_bit_array n r, Both

  (* Computes a remainder and modulo for the result of [v1 op v2]. *)
  let compute_modulo v1 v2 =
    let b1, s1 = low_bit_mask v1
    and b2, s2 = low_bit_mask v2 in
    let size = max (Array.length b1) (Array.length b2) in
    (* Sets the [i] nth bits of [rem] until an uncertainty appears. *)
    let rec step i rem =
      let b1 = try b1.(i) with _ -> s1
      and b2 = try b2.(i) with _ -> s2 in
      let b = Op.forward b1 b2 in
      if i >= size || b = Both
      then rem, Int.two_power_of_int i
      else
        (* [rem] starts at 0, so we only need to turn on the 1 bits. *)
        let rem = if b = On then set_bit_on ~size (Bit i) rem else rem in
        step (i+1) rem
    in
    step 0 Int.zero

  (* The number of bits on which the result should be significant *)
  let result_size (v1 : t) (v2 : t) : int option =
    let n1 = significant_bits v1 and n2 = significant_bits v2 in
    let n1_greater =
      match n1, n2 with
      | None, _ -> true
      | _, None -> false
      | Some n1, Some n2 -> n1 >= n2
    in
    (* whether n1 or n2 is greater, look if the sign bit oped with anything is
       not constant. If it is constant, then the highest bits are irrelevant. *)
    if n1_greater
    then if Op.forward Both (extract_sign v2) = Both then n1 else n2
    else if Op.forward (extract_sign v1) Both = Both then n2 else n1

  exception Do_not_fit_small_sets

  (* Try to build a small set.
     It is basically enumerating the possible results, by choosing the possible
     bits from left to right. This function aborts if it ever exceeds the small
     set size. The algorithm is probably not complete, as it is not always
     possible to reduce the operands leading to a result (without an
     exponential cost)  meaning that sometimes small sets can be obtained but
     the algorithm will fail to find them. *)
  let compute_small_set ~size (v1 : t) (v2 : t) (r : Int.t) (modu : Int.t) =
    let set_bit i acc (r, v1, v2) =
      let b1 = extract_bit i v1
      and b2 = extract_bit i v2 in
      match Op.forward b1 b2 with
      | On -> (set_bit_on ~size i r, v1, v2) :: acc
      | Off -> (r, v1, v2) :: acc
      | Both ->
        let v1_off = Bottom.non_bottom (reduce_bit i v1 (Op.backward_off b2))
        and v2_off = Bottom.non_bottom (reduce_bit i v2 (Op.backward_off b1)) in
        let v1_on = Bottom.non_bottom (reduce_bit i v1 (Op.backward_on b2))
        and v2_on = Bottom.non_bottom (reduce_bit i v2 (Op.backward_on b1)) in
        (set_bit_on ~size i r, v1_on, v2_on) :: (r, v1_off, v2_off) :: acc
    in
    let acc = ref (set_bit Sign [] (r, v1, v2)) in
    for i = size - 1 downto Z.numbits modu - 1 do
      acc := List.fold_left (set_bit (Bit i)) [] !acc;
      if List.length !acc > small_cardinal () then raise Do_not_fit_small_sets
    done;
    (* Keep only values that can actually be obtained *)
    let is_admissible (r, v1, v2) =
      match v1, v2 with
      | Set s1, Set s2 ->
        let op = Op.concrete_bitwise in
        Int_set.(exists (fun i1 -> exists (fun i2 -> op i1 i2 = r) s2) s1)
      | _, _ -> true
    in
    let list = Extlib.filter_map is_admissible (fun (r, _, _) -> r) !acc in
    Set (Int_set.inject_list list)

  (* If lower is true (resp. false), compute the lower (resp. upper) bound of
     the result interval when applying the bitwise operator to [v1] and [v2].
     [size] is the number of bits of the result.
     This function should be exact when the operands are small sets or tops
     with modulo 1. Otherwise, it is an overapproximation of the bound. *)
  let compute_bound ~size v1 v2 lower =
    (* Sets the [i]-nth bit of the currently computed bound [r] of [v1 op v2].
       If possible, reduces [v1] and [v2] accordingly. *)
    let set_bit i (r, v1, v2) =
      let b1 = extract_bit i v1
      and b2 = extract_bit i v2 in
      let b, v1, v2 =
        match Op.forward b1 b2 with
        | On | Off as b -> b, v1, v2 (* Constant bit, no reduction. *)
        | Both ->
          (* Choose the best bit for the searched bound, and reduces [v1] and
             [v2] accordingly. *)
          let b = match i with
            | Sign -> if lower then On else Off
            | Bit _ -> if lower then Off else On
          in
          let v1 = Bottom.non_bottom (reduce_bit i v1 (backward b2 b))
          and v2 = Bottom.non_bottom (reduce_bit i v2 (backward b1 b)) in
          b, v1, v2
      in
      (* Only sets 1 bit, as [r] is 0 at the beginning. *)
      let r = if b = On then set_bit_on ~size i r else r in
      r, v1, v2
    in
    (* The result is 0 at the beginning, and [set_bit] turns on the 1 bits. *)
    let r = ref (Int.zero, v1, v2) in
    (* Sets the sign bit, and then the bits from size to 0. *)
    r := set_bit Sign !r;
    for i = (size - 1) downto 0 do
      r := set_bit (Bit i) !r;
    done;
    let bound, _v1, _v2 = !r in
    bound

  let bitwise_forward (v1 : t) (v2 : t) : t =
    match v1, v2 with
    | Set s1, Set s2 ->
      inject_set_or_top (Int_set.apply2 Op.concrete_bitwise s1 s2)
    | _, _ ->
      let r, modu = compute_modulo v1 v2 in
      match result_size v1 v2 with
      | None ->
        (* We could do better here, as one of the bound may be finite. However,
           this case should occur rarely or not at all. *)
        inject_interval ~min:None ~max:None ~rem:r ~modu
      | Some size ->
        try compute_small_set ~size v1 v2 r modu
        with Do_not_fit_small_sets ->
          let min = compute_bound ~size v1 v2 true
          and max = compute_bound ~size v1 v2 false in
          inject_interval ~min:(Some min) ~max:(Some max) ~rem:r ~modu
end

let bitwise_or = let module M = BitwiseOperator (Or) in M.bitwise_forward
let bitwise_and = let module M = BitwiseOperator (And) in M.bitwise_forward
let bitwise_xor = let module M = BitwiseOperator (Xor) in M.bitwise_forward


(* --- Bitwise not --- *)

let bitwise_signed_not v =
  match v with
  | Itv _ -> add (neg v) minus_one (* [-v - 1] *)
  | Set s -> Set (Int_set.bitwise_signed_not s)

let bitwise_unsigned_not ~size v =
  let size = Int.of_int size in
  cast_int_to_int ~size ~signed:false (bitwise_signed_not v)
