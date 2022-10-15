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

type (_,_) eq = Eq : ('a,'a) eq

module type Key = sig
  type 'a key

  val create_key: string -> 'a key
  val eq_type : 'a key -> 'b key -> ('a, 'b) eq option

  val print: 'a key Pretty_utils.formatter
  val compare: 'a key -> 'b key -> int
  val equal: 'a key -> 'b key -> bool
  val hash : 'a key -> int
  val tag: 'a key -> int
end

module Key = struct
  type _ key = ..

  module type Key = sig
    type t
    type _ key += Key : t key
  end

  type 'a k = (module Key with type t = 'a)

  let create (type a) () =
    let module M = struct
      type t = a
      type _ key += Key : t key
    end in
    (module M : Key with type t = a)

  let eq_type (type a) (type b) (x : a k) (y : b k) : (a, b) eq option =
    let module A = (val x : Key with type t = a) in
    let module B = (val y : Key with type t = b) in
    match A.Key with
    | B.Key -> Some Eq
    | _     -> None
end

module Make () = struct

  type 'a key = { key: 'a Key.k;
                  tag: int;
                  name: string }

  let c = ref (-1)
  let id () = incr c; !c

  let create_key name =
    { key = Key.create ();
      tag = id ();
      name }

  let eq_type : type a b. a key -> b key -> (a, b) eq option = fun x y ->
    Key.eq_type x.key y.key

  let equal x y = x.tag = y.tag
  let compare x y = Stdlib.compare x.tag y.tag
  let hash x = x.tag
  let tag x = x.tag

  let print fmt x = Format.pp_print_string fmt x.name
end

module Key_Value = Make ()
module Key_Location = Make ()
module Key_Domain = Make ()

module type Shape = sig
  include Key
  type 'a data

  type 'a structure =
    | Unit : unit structure
    | Void : 'a structure
    | Leaf : 'a key * 'a data -> 'a structure
    | Node : 'a structure * 'b structure -> ('a * 'b) structure
    | Option : 'a structure * 'a -> 'a option structure

  val eq_structure: 'a structure -> 'b structure -> ('a, 'b) eq option
end

module Shape (Key: Key) (Data: sig type 'a t end) = struct
  include Key
  type 'a data = 'a Data.t

  type 'a structure =
    | Unit : unit structure
    | Void : 'a structure
    | Leaf : 'a key * 'a data -> 'a structure
    | Node : 'a structure * 'b structure -> ('a * 'b) structure
    | Option : 'a structure * 'a -> 'a option structure

  let rec eq_structure : type a b. a structure -> b structure -> (a, b) eq option
    = fun a b ->
      match a, b with
      | Leaf (key1, _), Leaf (key2, _) -> Key.eq_type key1 key2
      | Node (l1, r1), Node (l2, r2) ->
        begin
          match eq_structure l1 l2, eq_structure r1 r2 with
          | Some Eq, Some Eq -> Some Eq
          | _, _ -> None
        end
      | Option (s1, _), Option (s2, _) ->
        begin
          match eq_structure s1 s2 with
          | Some Eq -> Some Eq
          | None -> None
        end
      | Unit, Unit -> Some Eq
      | _, _ -> None
end

module type Internal = sig
  type t
  type 'a structure
  val structure : t structure
end

module type External = sig
  type t
  type 'a key
  type 'a data
  val mem : 'a key -> bool
  val get : 'a key -> (t -> 'a) option
  val set : 'a key -> 'a -> t -> t

  type polymorphic_iter_fun = {
    iter: 'a. 'a key -> 'a data -> 'a -> unit;
  }
  val iter: polymorphic_iter_fun -> t -> unit

  type 'b polymorphic_fold_fun = {
    fold: 'a. 'a key -> 'a data -> 'a -> 'b -> 'b;
  }
  val fold: 'b polymorphic_fold_fun -> t -> 'b -> 'b

  type polymorphic_map_fun = {
    map: 'a. 'a key -> 'a data -> 'a -> 'a;
  }
  val map: polymorphic_map_fun -> t -> t
end

module Open
    (Shape : Shape)
    (M : sig type t val structure : t Shape.structure end)
= struct

  module KMap = struct
    include Map.Make (Datatype.Int)

    let singleton key data = singleton (Shape.tag key) data
    let find k map =
      try Some (find (Shape.tag k) map)
      with Not_found -> None
  end

  open Shape

  let rec mem : type a. 'v Shape.key -> a structure -> bool = fun key -> function
    | Unit -> false
    | Void -> false
    | Leaf (k, _) -> Shape.equal key k
    | Node (left, right) -> mem key left || mem key right
    | Option (s, _) -> mem key s

  let mem key = mem key M.structure


  type ('a, 'b) get = 'b Shape.key * ('a -> 'b)

  type 'a getter = Get : ('a, 'b) get -> 'a getter

  let lift_get f (Get (key, get)) = Get (key, fun t -> get (f t))

  let rec compute_getters : type a. a structure -> (a getter) KMap.t = function
    | Unit -> KMap.empty
    | Void -> KMap.empty
    | Leaf (key, _) ->  KMap.singleton key (Get (key, fun (t : a) -> t))
    | Node (left, right) ->
      let l = compute_getters left and r = compute_getters right in
      let l = KMap.map (lift_get fst) l and r = KMap.map (lift_get snd) r in
      KMap.union (fun _k a _b -> Some a) l r
    | Option (s, default) ->
      let l = compute_getters s in
      KMap.map (lift_get (Option.value ~default:default)) l

  let getters = compute_getters M.structure
  let get (type a) (key: a Shape.key) : (M.t -> a) option =
    match KMap.find key getters with
    | None -> None
    | Some (Get (k, get)) -> match Shape.eq_type key k with
      | None -> None
      | Some Eq -> Some get


  type ('a, 'b) set = 'b Shape.key * ('b -> 'a -> 'a)

  type 'a setter = Set : ('a, 'b) set -> 'a setter

  let lift_set f (Set (key, set)) = Set (key, fun v b -> f (fun a -> set v a) b)

  let rec compute_setters : type a. a structure -> (a setter) KMap.t = function
    | Unit -> KMap.empty
    | Void -> KMap.empty
    | Leaf (key, _) -> KMap.singleton key (Set (key, fun v _t -> v))
    | Node (left, right) ->
      let l = compute_setters left and r = compute_setters right in
      let l = KMap.map (lift_set (fun set (l, r) -> set l, r)) l
      and r = KMap.map (lift_set (fun set (l, r) -> l, set r)) r in
      KMap.union (fun _k a _b -> Some a) l r
    | Option (s, _) ->
      let l = compute_setters s in
      KMap.map (lift_set Option.map) l

  let setters = compute_setters M.structure
  let set (type a) (key: a Shape.key) : (a -> M.t -> M.t) =
    match KMap.find key setters with
    | None -> fun _ t -> t
    | Some (Set (k, set)) -> match Shape.eq_type key k with
      | None -> fun _ t -> t
      | Some Eq -> set

  type polymorphic_iter_fun = {
    iter: 'a. 'a Shape.key -> 'a Shape.data -> 'a -> unit;
  }

  let rec iter: type a. a structure -> (polymorphic_iter_fun -> a -> unit) =
    function
    | Unit -> fun _ () -> ()
    | Void -> fun _ _ -> ()
    | Leaf (key, data) -> fun poly v -> poly.iter key data v
    | Node (left, right) ->
      let left = iter left
      and right = iter right in
      fun poly (a, b) -> left poly a; right poly b;
    | Option (s, _) ->
      let iter = iter s in
      fun poly v -> Option.iter (iter poly) v

  let iter = iter M.structure

  type 'b polymorphic_fold_fun = {
    fold: 'a. 'a Shape.key -> 'a Shape.data -> 'a -> 'b -> 'b;
  }

  let rec fold: type a. a structure -> ('b polymorphic_fold_fun -> a -> 'b -> 'b) =
    function
    | Unit -> fun _ () acc -> acc
    | Void -> fun _ _ acc -> acc
    | Leaf (key, data) -> fun poly v acc -> poly.fold key data v acc
    | Node (left, right) ->
      let left = fold left
      and right = fold right in
      fun poly (a, b) acc -> right poly b (left poly a acc)
    | Option (s, _) ->
      let fold = fold s in
      fun poly v acc -> Option.fold ~none:acc ~some:(fun v -> fold poly v acc) v

  let fold x = fold M.structure x

  type polymorphic_map_fun = {
    map: 'a. 'a Shape.key -> 'a Shape.data -> 'a -> 'a;
  }

  let rec map: type a. a structure -> (polymorphic_map_fun -> a -> a) =
    function
    | Unit -> fun _ () -> ()
    | Void -> fun _ x -> x
    | Leaf (key, data) -> fun poly v -> poly.map key data v
    | Node (left, right) ->
      let left = map left
      and right = map right in
      fun poly (a, b) -> (left poly a, right poly b)
    | Option (s, _) ->
      let map = map s in
      fun poly v -> Option.map (map poly) v

  let map = map M.structure
end
