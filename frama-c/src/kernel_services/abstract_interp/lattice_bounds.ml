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

type 'a or_bottom = [ `Value of 'a | `Bottom ]
type 'a or_top = [ `Value of 'a | `Top ]
type 'a or_top_bottom = [ `Value of 'a | `Bottom | `Top ]

(** Common functions *)

module Common =
struct

  (* Pretty-printing *)

  let pretty_top fmt =
    Format.pp_print_string fmt (Unicode.top_string ())

  let pretty_bottom fmt =
    Format.pp_print_string fmt (Unicode.bottom_string ())

  let pretty pretty_value fmt = function
    | `Bottom -> pretty_bottom fmt
    | `Top -> pretty_top fmt
    | `Value v -> pretty_value fmt v

  (* Datatype *)

  let hash hash_value = function
    | `Bottom  -> 7
    | `Top -> 13
    | `Value v -> hash_value v

  let equal equal_value x y =
    match x, y with
    | `Bottom, `Bottom -> true
    | `Top, `Top -> true
    | `Value vx, `Value vy -> equal_value vx vy
    | (`Value _ | `Bottom | `Top), (`Value _ | `Bottom | `Top) -> false

  let compare compare_value a b = match a, b with
    | `Bottom, `Bottom -> 0
    | `Bottom, (`Top | `Value _) -> -1
    | (`Top | `Value _), `Bottom -> 1
    | `Top, `Top -> 0
    | `Top, `Value _ -> -1
    | `Value _, `Top -> 1
    | `Value vx, `Value vy -> compare_value vx vy

  (* Tests *)

  let is_bottom = function
    | `Bottom -> true
    | `Value _ | `Top -> false

  let is_top = function
    | `Top -> true
    | `Value _ | `Bottom -> false

  let is_included is_included x y =
    match x, y with
    | `Bottom, _ | _, `Top -> true
    | _, `Bottom | `Top, _ -> false
    | `Value vx, `Value vy -> is_included vx vy

  (* Iterator *)
  let iter f = function
    | `Bottom | `Top -> ()
    | `Value v -> f v

  (* Conversion *)
  let to_option = function
    | `Bottom | `Top -> None
    | `Value x -> Some x

end

module Bottom = struct
  type 'a t = 'a or_bottom

  include Common

  (** Access *)

  let non_bottom = function
    | `Value v -> v
    | `Bottom  -> assert false

  let value ~bottom = function
    | `Value v -> v
    | `Bottom -> bottom

  (* Lattice operators *)

  let join join x y = match x, y with
    | `Value vx, `Value vy    -> `Value (join vx vy)
    | `Bottom, (`Value _ as v)
    | (`Value _ as v), `Bottom
    | (`Bottom as v), `Bottom -> v

  let join_list j l = List.fold_left (join j) `Bottom l

  let narrow narrow x y = match x, y with
    | `Value vx, `Value vy    -> narrow vx vy
    | `Bottom, `Value _
    | `Value _, `Bottom
    | `Bottom, `Bottom -> `Bottom

  (* Iterators *)

  let fold ~bottom f = function
    | `Bottom -> bottom
    | `Value v -> f v

  let map f = function
    | `Bottom -> `Bottom
    | `Value v -> `Value (f v)

  (* Combination *)

  let zip x y =
    match x, y with
    | `Bottom, _ | _, `Bottom -> `Bottom
    | `Value x, `Value y -> `Value (x,y)

  (** Conversion *)

  let of_option = function
    | None -> `Bottom
    | Some v -> `Value v

  let to_list = function
    | `Bottom  -> []
    | `Value v -> [v]

  let bot_of_list = function
    | [] -> `Bottom
    | l  -> `Value l

  let list_of_bot = function
    | `Bottom  -> []
    | `Value l -> l

  let add_to_list elt list = match elt with
    | `Bottom    -> list
    | `Value elt -> elt :: list

  let list_values l =
    List.fold_left (fun l elt -> add_to_list elt l) [] l

  (** Operators *)

  module Operators =
  struct
    let (>>-) t f = match t with
      | `Bottom  -> `Bottom
      | `Value t -> f t

    let (>>-:) t f = match t with
      | `Bottom  -> `Bottom
      | `Value t -> `Value (f t)

    let (let+) = (>>-:)
    let (and+) = zip
    let (let*) = (>>-)
    let (and*) = zip
  end

  (** Datatype construction *)
  let counter = ref 0

  module Make_Datatype
      (Domain: Datatype.S)
    =
    Datatype.Make (
    struct
      include Datatype.Serializable_undefined
      type t = Domain.t or_bottom
      let () = incr counter
      let name = Domain.name ^ "+bottom(" ^ string_of_int !counter ^ ")"
      let reprs = `Bottom :: (List.map (fun v -> `Value v) Domain.reprs)
      let structural_descr = Structural_descr.t_unknown
      let hash = Common.hash Domain.hash
      let equal = (Common.equal Domain.equal :> t -> t -> bool)
      let compare = Common.compare Domain.compare
      let rehash = Datatype.identity
      let copy = map Domain.copy
      let pretty = Common.pretty Domain.pretty
      let mem_project = Datatype.never_any_project
    end)

  (* Bound lattice *)

  module Bound_Lattice
      (Lattice: Lattice_type.Join_Semi_Lattice)
  = struct
    include Make_Datatype (Lattice)

    let bottom = `Bottom
    let join = join Lattice.join
    let is_included = is_included Lattice.is_included
  end
end


module Top =
struct
  type 'a t = 'a or_top

  include Common

  (** Access *)

  let non_top = function
    | `Value v -> v
    | `Top  -> assert false

  let value ~top = function
    | `Value v -> v
    | `Top -> top

  (** Lattice *)

  let join join_value x y =
    match x, y with
    | `Top, _ | _, `Top -> `Top
    | `Value vx, `Value vy -> join_value vx vy

  let narrow narrow_value x y =
    match x, y with
    | `Top, v | v, `Top -> v
    | `Value vx, `Value vy -> `Value (narrow_value vx vy)

  (** Combination *)

  let zip x y =
    match x, y with
    | `Top, _ | _, `Top -> `Top
    | `Value x, `Value y -> `Value (x,y)

  (** Conversion. *)

  let of_option = function
    | None -> `Top
    | Some x -> `Value x

  (** Operators *)

  module Operators = struct
    let (>>-) t f = match t with
      | `Top -> `Top
      | `Value t -> f t

    let (>>-:) t f = match t with
      | `Top -> `Top
      | `Value t -> `Value (f t)

    let (let+) = (>>-:)
    let (and+) = zip
    let (let*) = (>>-)
    let (and*) = zip
  end
end


module TopBottom =
struct
  type 'a t = 'a or_top_bottom

  include Common

  (* Lattice operators *)

  let join join_value x y = match x, y with
    | `Top, _ | _, `Top -> `Top
    | `Bottom, x | x, `Bottom -> x
    | `Value vx, `Value vy -> (join_value vx vy :> 'a t)

  let narrow narrow_value x y = match x, y with
    | `Top, v | v, `Top -> v
    | `Bottom, _ | _, `Bottom -> `Bottom
    | `Value vx, `Value vy -> (narrow_value vx vy :> 'a t)

  (** Combination *)

  let zip x y =
    match x, y with
    | `Bottom, _ | _, `Bottom -> `Bottom
    | `Top, _ | _, `Top -> `Top
    | `Value x, `Value y -> `Value (x,y)

  (** Operators *)

  module Operators = struct
    let (>>-) t f = match t with
      | `Top -> `Top
      | `Bottom -> `Bottom
      | `Value t -> f t

    let (>>-:) t f = match t with
      | `Top -> `Top
      | `Bottom -> `Bottom
      | `Value t -> `Value (f t)

    let (let+) = (>>-:)
    let (and+) = zip
    let (let*) = (>>-)
    let (and*) = zip
  end
end
