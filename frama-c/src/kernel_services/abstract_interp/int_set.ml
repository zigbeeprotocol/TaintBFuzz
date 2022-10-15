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

(* Make sure all this is synchronized with the default value of -ilevel *)
let small_cardinal = ref 8
let get_small_cardinal () = !small_cardinal
let set_small_cardinal i = small_cardinal := i

let debug_cardinal = false

let emitter = Lattice_messages.register "Int_set";;
let log_imprecision s = Lattice_messages.emit_imprecision emitter s

(* Small sets of integers, implemented as sorted non-empty arrays. *)
type set = Int.t array

(* Redefine functions creating arrays to forbid empty arrays and arrays with
   more elements than [!small_cardinal]. *)
module Array = struct
  include Array

  (* Do not warn on unused functions: all functions creating arrays should be
     refefined here, even if they are not used yet. *)
  [@@@ warning "-32"]

  (* This function creates a zero array of the same size as the array [a].
     No need to check the length as the [a] must already satisfies the
     invariants. *)
  let zero_copy a =
    let l = Array.length a in
    make l Int.zero, l

  let make n x = assert (n > 0 && n <= !small_cardinal); make n x
  let init n f = assert (n > 0 && n <= !small_cardinal); init n f
  let sub a start len = assert (len > 0); sub a start len
end

let zero = [| Int.zero |]
let one = [| Int.one |]
let minus_one = [| Int.minus_one |]
let zero_or_one = [| Int.zero ; Int.one |]

let inject_singleton e = [| e |]

let inject_periodic ~from ~period ~number =
  let l = Int.to_int_exn number in
  let s = Array.make l Int.zero in
  let v = ref from in
  let i = ref 0 in
  while (!i < l)
  do
    s.(!i) <- !v;
    v := Int.add period !v;
    incr i
  done;
  s

module O = Set.Make (Integer)

let inject_list list =
  let o = List.fold_left (fun o r -> O.add r o) O.empty list in
  let cardinal = O.cardinal o in
  let a = Array.make cardinal Int.zero in
  let i = ref 0 in
  O.iter (fun e -> a.(!i) <- e; incr i) o;
  a

let to_list = Array.to_list

(* ------------------------------- Datatype --------------------------------- *)

let hash s = Array.fold_left (fun acc v -> 1031 * acc + (Int.hash v)) 17 s

exception Unequal of int

let compare s1 s2 =
  let l1 = Array.length s1 in
  let l2 = Array.length s2 in
  if l1 <> l2
  then l1 - l2 (* no overflow here *)
  else
    (try
       for i = 0 to l1 - 1 do
         let r = Int.compare s1.(i) s2.(i) in
         if r <> 0 then raise (Unequal r)
       done;
       0
     with Unequal v -> v)

let equal e1 e2 = compare e1 e2 = 0

let pretty fmt s =
  Pretty_utils.pp_iter
    ~pre:"@[<hov 1>{"
    ~suf:"}@]"
    ~sep:";@ "
    Array.iter Int.pretty fmt s

include Datatype.Make_with_collections
    (struct
      type t = set
      let name = "int_set"
      open Structural_descr
      let structural_descr = t_array (Descr.str Int.descr)
      let reprs = [ zero ]
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

(* ---------------------------------- Utils --------------------------------- *)

let cardinal =
  if debug_cardinal
  then
    fun s ->
      let l = Array.length s in
      assert (l > 0 && l <= !small_cardinal);
      l
  else Array.length

let for_all f (a : Integer.t array) =
  let l = Array.length a in
  let rec c i = i = l || ((f a.(i)) && c (succ i)) in
  c 0

let exists = Array.exists

let iter = Array.iter
let fold ?(increasing=true) =
  if increasing
  then fun f array acc -> Array.fold_left (fun acc x -> f x acc) acc array
  else Array.fold_right

let truncate_no_bottom r i =
  if i = 1
  then inject_singleton r.(0)
  else Array.sub r 0 i

let truncate_or_bottom r i =
  if i = 0 then `Bottom else `Value (truncate_no_bottom r i)

let map_reduce (f : 'a -> 'b) (g : 'b -> 'b -> 'b) (set : 'a array) : 'b =
  let acc = ref (f set.(0)) in
  for i = 1 to Array.length set - 1 do
    acc := g !acc (f set.(i))
  done;
  !acc

let filter (f : Int.t -> bool) (a : Int.t array) : t or_bottom =
  let r, l = Array.zero_copy a in
  let j = ref 0 in
  for i = 0 to l  - 1 do
    let x = a.(i) in
    if f x then begin
      r.(!j) <- x;
      incr j;
    end
  done;
  truncate_or_bottom r !j

let mem v a =
  let l = Array.length a in
  let rec c i =
    if i = l then (-1)
    else
      let ae = a.(i) in
      if Int.equal ae v
      then i
      else if Int.gt ae v
      then (-1)
      else c (succ i)
  in
  c 0

(* ------------------------------- Set or top ------------------------------- *)

type set_or_top = [ `Set of t | `Top of Integer.t * Integer.t * Integer.t ]
type set_or_top_or_bottom = [ `Bottom | set_or_top ]

type pre_set =
  | Pre_set of O.t * int
  | Pre_top of Int.t * Int.t * Int.t

let empty_ps = Pre_set (O.empty, 0)

let make_top_from_set s =
  if debug_cardinal then assert (O.cardinal s >= 2);
  let min = O.min_elt s in
  let max = O.max_elt s in
  let modu = O.fold
      (fun x acc ->
         if Int.equal x min then acc else Int.pgcd (Int.sub x min) acc)
      s Int.zero
  in
  (min, max, modu)

let add_ps ps x =
  match ps with
  | Pre_set (o, s) ->
    if debug_cardinal then assert (O.cardinal o = s);
    if O.mem x o (* TODO: improve *)
    then ps
    else
      let no = O.add x o in
      if s < !small_cardinal
      then begin
        if debug_cardinal then assert (O.cardinal no = succ s);
        Pre_set (no, succ s)
      end
      else
        let min, max, modu =  make_top_from_set no in
        Pre_top (min, max, modu)
  | Pre_top (min, max, modu) ->
    let new_modu =
      if Int.equal x min
      then modu
      else Int.pgcd (Int.sub x min) modu
    in
    let new_min = Int.min min x in
    let new_max = Int.max max x in
    Pre_top (new_min, new_max, new_modu)

let share_set o s =
  let a = Array.make s Int.zero in
  let i = ref 0 in
  O.iter (fun e -> a.(!i) <- e; incr i) o;
  assert (!i = s);
  a

let inject_ps = function
  | Pre_set (o, s) -> `Set (share_set o s)
  | Pre_top (min, max, modu) -> `Top (min, max, modu)

let inject_ps_or_bottom = function
  | Pre_set (o, s) -> if s = 0 then `Bottom else `Set (share_set o s)
  | Pre_top (min, max, modu) -> `Top (min, max, modu)

(* Given a set of elements that is an under-approximation, returns an
   ival (while maintaining the ival invariants that the "Set"
   constructor is used only for small sets of elements. *)
let set_to_ival_under set =
  let card = Int.Set.cardinal set in
  if card <= !small_cardinal
  then
    let a = Array.make card Int.zero in
    ignore (Int.Set.fold (fun elt i -> Array.set a i elt; i + 1) set 0);
    `Set a
  else
    (* If by chance the set is contiguous. *)
  if (Int.equal
        (Int.sub (Int.Set.max_elt set) (Int.Set.min_elt set))
        (Int.of_int (card - 1)))
  then `Top (Int.Set.min_elt set, Int.Set.max_elt set, Int.one)
  (* Else: arbitrarily drop some elements of the under approximation. *)
  else
    let a = Array.make !small_cardinal Int.zero in
    log_imprecision "Ival.set_to_ival_under";
    try
      ignore (Int.Set.fold (fun elt i ->
          if i = !small_cardinal then raise Exit;
          Array.set a i elt;
          i + 1) set 0);
      assert false
    with Exit -> `Set a

(* ------------------------------ Apply and map ----------------------------- *)

let apply_bin_1_strict_incr f x (s : Integer.t array) =
  let r, l = Array.zero_copy s in
  let rec c i =
    if i = l
    then r
    else
      let v = f x s.(i) in
      r.(i) <- v;
      c (succ i)
  in
  c 0

let apply_bin_1_strict_decr f x (s : Integer.t array) =
  let r, l = Array.zero_copy s in
  let rec c i =
    if i = l
    then r
    else
      let v = f x s.(i) in
      r.(l - i - 1) <- v;
      c (succ i)
  in
  c 0

let apply2 f (s1 : Integer.t array) (s2 : Integer.t array) =
  let ps = ref empty_ps in
  let l1 = Array.length s1 in
  let l2 = Array.length s2 in
  for i1 = 0 to pred l1 do
    let e1 = s1.(i1) in
    for i2 = 0 to pred l2 do
      ps := add_ps !ps (f e1 s2.(i2))
    done
  done;
  inject_ps !ps

let apply2_notzero f (s1 : Integer.t array) s2 =
  inject_ps_or_bottom
    (Array.fold_left
       (fun acc v1 ->
          Array.fold_left
            (fun acc v2 ->
               if Int.is_zero v2
               then acc
               else add_ps acc (f v1 v2))
            acc
            s2)
       empty_ps
       s1)

let map_set_decr f (s : Integer.t array) =
  let r, l = Array.zero_copy s in
  let rec c srcindex dstindex last =
    if srcindex < 0
    then begin
      r.(dstindex) <- last;
      truncate_no_bottom r (succ dstindex)
    end
    else
      let v = f s.(srcindex) in
      if Int.equal v last
      then
        c (pred srcindex) dstindex last
      else begin
        r.(dstindex) <- last;
        c (pred srcindex) (succ dstindex) v
      end
  in
  c (l-2) 0 (f s.(pred l))

let map_set_strict_decr f (s : Integer.t array) =
  let r, l = Array.zero_copy s in
  let rec c i =
    if i = l
    then r
    else
      let v = f s.(i) in
      r.(l - i - 1) <- v;
      c (succ i)
  in
  c 0

let map_set_incr f (s : Integer.t array) =
  let r, l = Array.zero_copy s in
  let rec c srcindex dstindex last =
    if srcindex = l
    then begin
      r.(dstindex) <- last;
      truncate_no_bottom r (succ dstindex)
    end
    else
      let v = f s.(srcindex) in
      if Int.equal v last
      then
        c (succ srcindex) dstindex last
      else begin
        r.(dstindex) <- last;
        c (succ srcindex) (succ dstindex) v
      end
  in
  c 1 0 (f s.(0))

let map f s =
  let pre_set =
    Array.fold_left (fun acc elt -> add_ps acc (f elt)) empty_ps s
  in
  match pre_set with
  | Pre_set (o, s) -> share_set o s
  | Pre_top _ -> assert false

(* --------------------------------- Lattice -------------------------------- *)

let is_included s1 s2 =
  let l1 = Array.length s1 in
  let l2 = Array.length s2 in
  if l1 > l2 then false
  else
    let rec c i1 i2 =
      if i1 = l1 then true
      else if i2 = l2 then false
      else
        let e1 = s1.(i1) in
        let e2 = s2.(i2) in
        let si2 = succ i2 in
        if Int.equal e1 e2
        then c (succ i1) si2
        else if Int.lt e1 e2
        then false
        else c i1 si2 (* TODO: improve by not reading a1.(i1) all the time *)
    in
    c 0 0

(* Join [s1] of length [l1] and [s2] of length [l2]. *)
let join l1 s1 l2 s2 =
  (* first pass: count unique elements and detect inclusions *)
  let rec first i1 i2 uniq inc1 inc2 =
    if i1 = l1
    then (uniq + l2 - i2), false, inc2
    else if i2 = l2
    then (uniq + l1 - i1), inc1, false
    else
      let e1 = s1.(i1) in
      let e2 = s2.(i2) in
      if Int.lt e2 e1
      then first i1 (succ i2) (succ uniq) false inc2
      else if Int.gt e2 e1
      then first (succ i1) i2 (succ uniq) inc1 false
      else first (succ i1) (succ i2) (succ uniq) inc1 inc2
  in
  let uniq, incl1, incl2 = first 0 0 0 true true in
  if incl1 then `Set s1 else
  if incl2 then `Set s2 else
    (* second pass: make a set or make a top *)
  if uniq > !small_cardinal
  then
    let min = Int.min s1.(0) s2.(0) in
    let accum acc x =
      if Int.equal x min
      then acc
      else Int.pgcd (Int.sub x min) acc
    in
    let modu = ref Int.zero in
    for j = 0 to pred l1 do
      modu := accum !modu s1.(j)
    done;
    for j = 0 to pred l2 do
      modu := accum !modu s2.(j)
    done;
    `Top (min, Int.max s1.(pred l1) s2.(pred l2), !modu)
  else
    let r = Array.make uniq Int.zero in
    let rec c i i1 i2 =
      if i1 = l1
      then begin
        Array.blit s2 i2 r i (l2 - i2);
        r
      end
      else if i2 = l2
      then begin
        Array.blit s1 i1 r i (l1 - i1);
        r
      end
      else
        let si = succ i in
        let e1 = s1.(i1) in
        let e2 = s2.(i2) in
        if Int.lt e2 e1
        then begin
          r.(i) <- e2;
          c si i1 (succ i2)
        end
        else begin
          r.(i) <- e1;
          let si1 = succ i1 in
          if Int.equal e1 e2
          then c si si1 (succ i2)
          else c si si1 i2
        end
    in
    `Set (c 0 0 0)

let join s1 s2 =
  let l1 = Array.length s1 in
  let l2 = Array.length s2 in
  if debug_cardinal then assert (l1 > 0 && l2 > 0);
  join l1 s1 l2 s2

let link s1 s2 =
  let s1 = Array.fold_right Int.Set.add s1 Int.Set.empty in
  let s2 = Array.fold_right Int.Set.add s2 s1 in
  set_to_ival_under s2

let meet s1 s2 =
  let l1 = Array.length s1 in
  let l2 = Array.length s2 in
  let lr_max = min l1 l2 in
  let r = Array.make lr_max Int.zero in
  let rec c i i1 i2 =
    if i1 = l1 || i2 = l2
    then truncate_or_bottom r i
    else
      let e1 = s1.(i1) in
      let e2 = s2.(i2) in
      if Int.equal e1 e2
      then begin
        r.(i) <- e1;
        c (succ i) (succ i1) (succ i2)
      end
      else if Int.lt e1 e2
      then c i (succ i1) i2
      else c i i1 (succ i2)
  in
  c 0 0 0

let narrow = meet (* meet is exact. *)

let intersects s1 s2 =
  let l1 = Array.length s1 in
  let l2 = Array.length s2 in
  let rec aux i1 i2 =
    if i1 = l1 || i2 = l2 then false
    else
      let e1 = s1.(i1) in
      let e2 = s2.(i2) in
      if Int.equal e1 e2 then true
      else if Int.lt e1 e2 then aux (succ i1) i2
      else aux i1 (succ i2)
  in
  aux 0 0

let diff_if_one _value _rem = assert false

let remove s v =
  let index = mem v s in
  if index >= 0
  then
    let l = pred (Array.length s) in
    if l <= 0 then `Bottom else
      let r = Array.make l Int.zero in
      Array.blit s 0 r 0 index;
      Array.blit s (succ index) r index (l-index);
      `Value r
  else `Value s

let complement_under ~min ~max set =
  let l = Array.length set in
  let get idx =
    if idx < 0 then Int.pred min
    else if idx >= l then Int.succ max
    else set.(idx)
  in
  let index = ref (-1) in
  let max_delta = ref Int.zero in
  for i = 0 to l do
    let delta = Int.pred (Int.sub (get i) (get (i-1))) in
    if Int.gt delta !max_delta then begin
      index := i;
      max_delta := delta
    end
  done;
  let b, e = Int.succ (get (!index-1)), Int.pred (get !index) in
  let card = Int.succ (Int.sub e b) in
  if Int.(le card zero) then `Bottom
  else if Int.le card (Int.of_int !small_cardinal)
  then `Set (Array.init (Int.to_int_exn card) (fun i -> Int.add b (Int.of_int i)))
  else `Top (b, e, Int.one)

(* ------------------------------ Arithmetics ------------------------------- *)

let add_singleton = apply_bin_1_strict_incr Int.add

let add s1 s2 =
  match s1, s2 with
  | [| x |], s | s, [| x |] -> `Set (apply_bin_1_strict_incr Int.add x s)
  | _, _ -> apply2 Int.add s1 s2

let add_under s1 s2 =
  match s1, s2 with
  | [| x |], s | s, [| x |] -> `Set (apply_bin_1_strict_incr Int.add x s)
  | _, _ ->
    let set =
      Array.fold_left (fun acc i1 ->
          Array.fold_left (fun acc i2 ->
              Int.Set.add (Int.add i1 i2) acc) acc s2)
        Int.Set.empty s1
    in
    set_to_ival_under set

let neg s = map_set_strict_decr Int.neg s

let abs s =
  if Int.(ge s.(0) zero)
  then s
  else if Int.(le s.(Array.length s - 1) zero)
  then neg s
  else map Int.abs s

let scale f s =
  if Int.ge f Int.zero
  then apply_bin_1_strict_incr Int.mul f s
  else apply_bin_1_strict_decr Int.mul f s

let mul s1 s2 =
  match s1, s2 with
  | s, [| x |] | [| x |], s -> `Set (scale x s)
  | _, _ -> apply2 Int.mul s1 s2

let scale_div ~pos f s =
  assert (not (Int.is_zero f));
  let div_f =
    if pos
    then fun a -> Int.e_div a f
    else fun a -> Int.c_div a f
  in
  if Int.lt f Int.zero
  then map_set_decr div_f s
  else map_set_incr div_f s

let scale_rem ~pos f s =
  assert (not (Int.is_zero f));
  let f = if Int.lt f Int.zero then Int.neg f else f in
  let rem_f a = if pos then Int.e_rem a f else Int.c_rem a f in
  map rem_f s

let c_rem s1 s2 = apply2_notzero Int.c_rem s1 s2

let bitwise_signed_not = map_set_strict_decr Int.lognot

(* ------------------------------- Subdivide -------------------------------- *)

let subdivide s =
  let len = Array.length s in
  if len <= 1 then raise Can_not_subdiv;
  let m = len lsr 1 in
  let lenhi = len - m in
  let lo = Array.sub s 0 m in
  let hi = Array.sub s m lenhi in
  lo, hi

(* -------------------------------- Export ---------------------------------- *)

let min t = t.(0)
let max t = t.(Array.length t - 1)

let mem i t = mem i t >= 0
