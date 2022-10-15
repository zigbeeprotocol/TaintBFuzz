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

type index = Integer.t * (Integer.t * Integer.t) list (* o, [dᵢ,bᵢ]ᵢ *)

module Term =
struct
  type t = Integer.t * Integer.t

  let pretty fmt (d,b : t) =
    Format.fprintf fmt "%a×[..%a]" Integer.pretty d Integer.pretty b

  let order (d1,_b1 : t) (d2,_b2 : t) = (* descending order *)
    Integer.compare d2 d1

  (* Keep the same interval but change the dimension (leading to
     over-approximation, hence coarcer abstraction). This might
     produce two terms instead of one *)
  let coarsen (d,b : t) (d' : Integer.t) =
    (* d×[0,b] -> (d'q + r)×[0,b] -> d'×[0,qb] + r×[0,b] *)
    let q,r = Integer.e_div_rem d d' in
    if Integer.is_zero r
    then [ (d', Integer.mul q b) ]
    else [ (d', Integer.mul q b) ; (r,b) ]

  let mul (d1,b1 : t) (d2,b2 : t) =
    Integer.mul d1 d2, Integer.mul b1 b2

  let mul_integer (i : Integer.t) (d,b : t) =
    Integer.mul d i, b
end

module Terms =
struct
  let hull sum =
    List.fold_left (fun acc (d,b) -> Integer.(add acc (mul d b))) Integer.zero sum

  (* Normalization *)

  let reorder sum =
    List.sort Term.order sum

  let merge sum1 sum2 =
    List.merge Term.order sum1 sum2

  let normalize sum = (* sum must be sorted in descending order *)
    let rec aux acc = function
      | [] -> acc
      | [term] -> term :: acc
      | (d1,b1) :: (((d2,b2) :: l) as tail) -> (* Descending order : d1 > d2 *)
        if Integer.equal d1 d2
        then aux ((d1,Integer.add b1 b2) :: acc) l (* merge terms together *)
        else if Integer.(lt (hull tail) d1)
        then aux ((d1,b1) :: acc) tail (* do nothing *)
        else aux acc (merge (Term.coarsen (d1,b1) d2) tail) (* coarsen d1 -> d2 *)
    in
    List.rev (aux [] sum)

  let mul_term (d,b) sum =
    List.map (Term.mul (d,b)) sum
end

module Prototype =
struct
  include Datatype.Undefined

  type t = index

  let name = "Multidim.SimplerIndex"

  let pretty fmt (o,sum) =
    Format.fprintf fmt "%a + %a"
      Integer.pretty o
      (Pretty_utils.pp_list ~sep:" +@ " Term.pretty) sum

  let reprs = [(Integer.zero,[])]
end

include Datatype.Make (Prototype)

(* Constructors *)

let zero = (Integer.zero,[])

let of_integer i =
  (i,[])

let of_int i =
  (Integer.of_int i,[])

let of_ival ival =
  try
    (Ival.project_int ival,[])
  with Ival.Not_Singleton_Int ->
  match Ival.min_max_r_mod ival with (* Raises Abstract_interp.Error_Bottom *)
  | None,_,_,_ | _,None,_,_ -> raise Abstract_interp.Error_Top
  | Some l, Some u, _r, m ->
    let u' = Integer.(c_div (sub u l) m) in
    (l,[m,u'])

(* Properties *)

let is_zero = function
  | o,[] when Integer.is_zero o -> true
  | _ -> false

let is_singleton = function
  | _o,[] -> true
  | _ -> false

let hull (o,sum) =
  o, Terms.hull sum

(* Decomposition *)

let first_dimension (o,sum) =
  match sum with
  | [] -> None
  | (d,_b) :: tail ->
    (* If normalized, no need to look in tail *)
    Some (d, (Integer.e_rem o d,tail))

(* Arithmetic *)

let add (o1,sum1) (o2,sum2) =
  Integer.add o1 o2, Terms.(normalize (merge sum1 sum2))

let add_integer (o,sum) i =
  (Integer.add o i, sum)

let add_int x i =
  add_integer x (Integer.of_int i)

let sub_integer (o,sum) i =
  (Integer.sub o i, sum)

let sub_int x i =
  sub_integer x (Integer.of_int i)

let mul (o1,sum1) (o2,sum2) =
  let sums =
    List.map (Term.mul_integer o1) sum2 ::
    List.map (Term.mul_integer o2) sum1 ::
    List.map (fun t1 -> Terms.mul_term t1 sum2) sum1
  in
  let sum = List.fold_left Terms.merge [] sums in
  Integer.mul o1 o2, Terms.normalize sum

let mul_integer (o,sum) i =
  Integer.mul o i, List.map (Term.mul_integer i) sum

let mul_int x i =
  mul_integer x (Integer.of_int i)

let mod_integer (o,sum) i =
  (* mod everything *)
  let o = Integer.e_rem o i in
  let sum = Extlib.filter_map'
      (fun (d,b) -> Integer.e_rem d i, b)
      (fun (d,_b) -> not (Integer.is_zero d))
      sum
  in
  let sum = Terms.(normalize (reorder sum)) in (* order was not preserverd *)
  (* We must then ensure that the set of represented offset is < i,
     i.e. that the highest possible value is < i.
     After normalization, this reduces to check that d*b + o < i.
     If it is not the case, we coarcen (d,b) to d' = pgcd(d,i) and use the
     greatest possible b' = i / d' *)
  match sum with
  | [] -> (o,[])
  | (d,b) :: tail ->
    if Integer.(lt (add (mul d b) o) i)
    then (o,sum) (* hull is ok, this is our result *)
    else
      let d' = Integer.pgcd d i in
      let b' = Integer.(pred (e_div i d')) in
      let o' = Integer.e_rem o d' in
      o', Terms.(normalize (merge [(d',b')] tail))

let mod_int x i =
  mod_integer x (Integer.of_int i)

(* Conversion from Cil *)

let rec of_exp oracle = function
  | { Cil_types.enode=BinOp (PlusA,e1,e2,_typ) } ->
    add (of_exp oracle e1) (of_exp oracle e2)
  | { enode=BinOp (Mult,e1,e2,_typ) } ->
    mul (of_exp oracle e1) (of_exp oracle e2)
  | { enode=BinOp (Shiftlt,e1,e2,_typ) } as expr ->
    begin match oracle e2 with
      | (i,[]) -> mul_integer (of_exp oracle e1) (Integer.two_power i)
      | _ -> oracle expr (* default to oracle *)
    end
  | expr -> oracle expr (* default to oracle *)

let of_offset oracle base_typ offset =
  let rec aux base_typ base_size x = function
    | Cil_types.NoOffset -> x, base_size
    | Field (fi, sub) ->
      let field_offset, field_size = Cil.fieldBitsOffset fi in
      aux fi.ftype (Integer.of_int field_size) (add_int x field_offset) sub
    | Index (exp, sub) ->
      match base_typ with
      | TArray (elem_typ, _array_size, _) ->
        let idx = of_exp oracle exp in
        let elem_size = Integer.of_int (Cil.bitsSizeOf elem_typ) in
        let x' = add x (mul_integer idx elem_size) in
        aux elem_typ elem_size x' sub
      | _ -> assert false (* Index is only valid on arrays *)
  in
  let base_size = Integer.of_int (Cil.bitsSizeOf base_typ) in
  fst (aux base_typ base_size zero offset)
