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

(* Ocaml compiler incorrectly considers that module MemorySafe is unused and
   emits a warning *)
[@@@warning "-60"]

open Lattice_bounds
open Abstract_offset
open Abstract_memory

module Bound = Segmentation.Bound

(* Composition operator for compare function *)

let (<?>) c lcmp =
  if c = 0 then 0 else Lazy.force lcmp

(* Types compatibility *)

let typ_size t = (* raises Cil.SizeOfError *)
  Integer.of_int (Cil.bitsSizeOf t)

let are_typ_compatible t1 t2 =
  Cil_datatype.TypNoAttrs.equal t1 t2 ||
  try Integer.equal (typ_size t1) (typ_size t2)
  with Cil.SizeOfError _ -> false

(* Input modules *)

module type Config =
sig
  val deps : State.t list
  val slice_limit : unit -> int
  val disjunctive_invariants : unit -> bool
end

module type Value =
sig
  type t

  val name : string

  val hash : t -> int
  val equal : t -> t -> bool
  val compare : t -> t -> int

  val pretty : Format.formatter -> t -> unit
  val of_bit : typ:Cil_types.typ -> bit -> t
  val to_bit : t -> bit
  val to_integer : t -> Integer.t option
  val is_included : t -> t -> bool
  val join : t -> t -> t
end


module Make (Config : Config) (V : Value) =
struct
  (* Recursively instanciate the typed memory *)
  module rec ProtoMemory : ProtoMemory with type value = V.t =
  struct
    type value = V.t

    type t =
      | Raw of bit
      | Scalar of memory_scalar
      | Struct of memory_struct
      | Disjunct of memory_disjunct
      | Union of memory_union
      | Array of memory_array
    and memory_scalar = {
      scalar_value: V.t;
      scalar_type: Cil_types.typ;
    }
    and memory_struct = {
      struct_value: S.t;
      struct_type: Cil_types.compinfo;
    }
    and memory_disjunct = {
      disj_value: D.t;
      disj_type: Cil_types.compinfo;
    }
    (* unions are handled separately from struct to avoid confusion and error *)
    and memory_union = {
      union_value: t;
      union_field: Cil_types.fieldinfo;
      union_padding: bit;
    }
    and memory_array = {
      array_value: A.t;
      array_cell_type: Cil_types.typ;
    }


    let are_scalar_compatible s1 s2 =
      are_typ_compatible s1.scalar_type s2.scalar_type

    let are_aray_compatible a1 a2 =
      are_typ_compatible a1.array_cell_type a2.array_cell_type

    let are_compinfo_compatible ci1 ci2 =
      ci1.Cil_types.ckey = ci2.Cil_types.ckey

    let are_structs_compatible s1 s2 =
      s1.struct_type.ckey = s2.struct_type.ckey

    let are_disjuncts_compatible d1 d2 =
      d1.disj_type.ckey = d2.disj_type.ckey

    let are_union_compatible u1 u2 =
      Cil_datatype.Fieldinfo.equal u1.union_field u2.union_field

    let rec pp ~root fmt =
      let prefix fmt =
        if not root then Format.fprintf fmt " = "
      in
      function
      | Raw b ->
        Format.fprintf fmt "%t%a" prefix Bit.pretty b
      | Scalar { scalar_value } ->
        Format.fprintf fmt "%t%a" prefix V.pretty scalar_value
      | Struct s ->
        Format.fprintf fmt "%t%a" prefix S.pretty s.struct_value
      | Disjunct d ->
        Format.fprintf fmt "%t%a" prefix D.pretty d.disj_value
      | Union u ->
        Format.fprintf fmt ".%s%a"
          u.union_field.Cil_types.fname
          (pp ~root:false) u.union_value
      | Array a ->
        Format.fprintf fmt "%a" A.pretty a.array_value

    let pretty fmt m = pp ~root:false fmt m
    let pretty_root fmt m =
      Format.fprintf fmt "@[<hv>%a@]" (pp ~root:true) m

    let rec hash m = match m with
      | Raw b -> Hashtbl.hash (
          1,
          Bit.hash b)
      | Scalar s -> Hashtbl.hash (
          2,
          V.hash s.scalar_value,
          Cil_datatype.Typ.hash s.scalar_type)
      | Struct s -> Hashtbl.hash (
          3,
          S.hash s.struct_value,
          Cil_datatype.Compinfo.hash s.struct_type)
      | Disjunct d -> Hashtbl.hash (
          4,
          D.hash d.disj_value,
          Cil_datatype.Compinfo.hash d.disj_type
        )
      | Union u -> Hashtbl.hash (
          5,
          hash u.union_value,
          Cil_datatype.Fieldinfo.hash u.union_field,
          Bit.hash u.union_padding)
      | Array a -> Hashtbl.hash (
          6,
          A.hash a.array_value,
          Cil_datatype.Typ.hash a.array_cell_type)

    let rec equal m1 m2 =
      match m1, m2 with
      | Raw b1, Raw b2 -> Bit.equal b1 b2
      | Scalar s1, Scalar s2 ->
        V.equal s1.scalar_value s2.scalar_value &&
        Cil_datatype.Typ.equal s1.scalar_type s2.scalar_type
      | Struct s1, Struct s2 ->
        S.equal s1.struct_value s2.struct_value &&
        Cil_datatype.Compinfo.equal s1.struct_type s2.struct_type
      | Disjunct d1, Disjunct d2 ->
        D.equal d1.disj_value d2.disj_value &&
        Cil_datatype.Compinfo.equal d1.disj_type d2.disj_type
      | Union u1, Union u2 ->
        equal u1.union_value u2.union_value &&
        Bit.equal u1.union_padding u2.union_padding &&
        Cil_datatype.Fieldinfo.equal u1.union_field u2.union_field
      | Array a1, Array a2 ->
        A.equal a1.array_value a2.array_value &&
        Cil_datatype.Typ.equal a1.array_cell_type a2.array_cell_type
      | (Raw _ | Scalar _ | Struct _ | Disjunct _ |  Union _ | Array _), _ ->
        false

    let rec compare m1 m2 =
      match m1, m2 with
      | Raw b1, Raw b2 -> Bit.compare b1 b2
      | Scalar s1, Scalar s2 ->
        V.compare s1.scalar_value s2.scalar_value <?>
        lazy (Cil_datatype.Typ.compare s1.scalar_type s2.scalar_type)
      | Struct s1, Struct s2 ->
        S.compare s1.struct_value s2.struct_value <?>
        lazy (Cil_datatype.Compinfo.compare s1.struct_type s2.struct_type)
      | Disjunct d1, Disjunct d2 ->
        D.compare d1.disj_value d2.disj_value <?>
        lazy (Cil_datatype.Compinfo.compare d1.disj_type d2.disj_type)
      | Union u1, Union u2 ->
        compare u1.union_value u2.union_value <?>
        lazy (Bit.compare u1.union_padding u2.union_padding) <?>
        lazy (Cil_datatype.Fieldinfo.compare u1.union_field u2.union_field)
      | Array a1, Array a2 ->
        A.compare a1.array_value a2.array_value <?>
        lazy (Cil_datatype.Typ.compare a1.array_cell_type a2.array_cell_type)
      | Raw _, _ -> 1
      | _, Raw _ -> -1
      | Scalar _, _ -> 1
      | _, Scalar _ -> -1
      | Struct _, _ -> 1
      | _, Struct _ -> -1
      | Disjunct _, _ -> 1
      | _, Disjunct _ -> -1
      | Union _, _ -> 1
      | _, Union _ -> -1

    let of_raw b = Raw b

    let rec raw m = match m with
      | Raw b -> b
      | Scalar s -> V.to_bit s.scalar_value
      | Struct s -> S.raw s.struct_value
      | Disjunct d -> D.raw d.disj_value
      | Union u -> raw u.union_value
      | Array a -> A.raw a.array_value

    let of_value scalar_type scalar_value =
      Scalar { scalar_type ; scalar_value }

    let to_value typ = function
      | Scalar s when are_typ_compatible s.scalar_type typ -> s.scalar_value
      | m -> V.of_bit ~typ (raw m)

    let rec to_singleton_int = function
      | Scalar s -> V.to_integer s.scalar_value
      | Raw (Zero _) -> Some Integer.zero
      | Union u -> to_singleton_int u.union_value
      | _ -> None

    let rec weak_erase b = function
      | Raw b' ->
        Raw (Bit.join b' b)
      | Scalar s when Bit.is_any b ->
        Raw (Bit.join (V.to_bit s.scalar_value) b)
      | Scalar s ->
        let typ = s.scalar_type in
        Scalar { s with scalar_value = V.(join (of_bit ~typ b) s.scalar_value) }
      | Array a ->
        Array { a with array_value = A.weak_erase b a.array_value }
      | Struct s ->
        Struct { s with struct_value = S.weak_erase b s.struct_value }
      | Disjunct d ->
        Disjunct { d with disj_value = D.weak_erase d.disj_type b d.disj_value }
      | Union u -> Union {
          u with
          union_padding = Bit.join u.union_padding b;
          union_value = weak_erase b u.union_value;
        }

    let rec is_included m1 m2 = match m1, m2 with
      | _, Raw r -> Bit.is_included (raw m1) r
      | Scalar s1, Scalar s2 ->
        are_scalar_compatible s1 s2 &&
        V.is_included s1.scalar_value s2.scalar_value
      | Array a1, Array a2 ->
        are_aray_compatible a1 a2 &&
        A.is_included a1.array_value a2.array_value
      | Struct s1, Struct s2 ->
        are_structs_compatible s1 s2 &&
        S.is_included s1.struct_value s2.struct_value
      | Disjunct d1, Disjunct d2 ->
        are_disjuncts_compatible d1 d2 &&
        D.is_included d1.disj_value d2.disj_value
      | Union u1, Union u2 ->
        are_union_compatible u1 u2 &&
        Bit.is_included u1.union_padding u2.union_padding &&
        is_included u1.union_value u2.union_value
      | (Raw _ | Scalar _ | Array _ | Struct _ | Disjunct _ | Union _), _ ->
        false

    let to_struct ~oracle ci = function
      | Struct s when are_compinfo_compatible s.struct_type ci ->
        s.struct_value
      | Disjunct d when are_compinfo_compatible d.disj_type ci ->
        D.to_struct ~oracle d.disj_value
      | m -> S.of_raw (raw m)

    let to_disj ci = function
      | Struct s when are_compinfo_compatible s.struct_type ci ->
        D.of_struct ci s.struct_value
      | Disjunct d when are_compinfo_compatible d.disj_type ci ->
        d.disj_value
      | m -> D.of_raw ci (raw m)

    let unify ~oracle f =
      let open Top.Operators in
      let raw_to_array side prototype b =
        A.hull ~oracle:(oracle side) prototype >>-:
        fun (l,u) -> A.single b l u (Raw b)
      in
      let rec aux m1 m2 =
        match m1, m2 with
        | Raw b1, Raw b2 -> Raw (Bit.join b1 b2)
        | Scalar s1, Scalar s2
          when are_typ_compatible s1.scalar_type s2.scalar_type ->
          let size = typ_size s1.scalar_type in
          let scalar_value = f ~size s1.scalar_value s2.scalar_value in
          Scalar { s1 with scalar_value }
        | Array a1, Array a2 when are_aray_compatible a1 a2 ->
          begin match A.unify ~oracle aux a1.array_value a2.array_value with
            | `Top -> Raw (Bit.join (raw m1) (raw m2))
            | `Value array_value -> Array { a1 with array_value }
          end
        | Array a1, Raw b2 ->
          let m =
            let* array_value2 = raw_to_array Left a1.array_value b2 in
            let+ array_value = A.unify ~oracle aux a1.array_value array_value2 in
            Array { a1 with array_value }
          in
          begin match m with
            | `Top -> weak_erase b2 (Array a1) (* Should not happen unless oracle is very unprecise *)
            | `Value m -> m
          end
        | Raw b1, Array a2 ->
          let m =
            let* array_value1 = raw_to_array Right a2.array_value b1 in
            let+ array_value = A.unify ~oracle aux array_value1 a2.array_value in
            Array { a2 with array_value }
          in
          begin match m with
            | `Top -> weak_erase b1 (Array a2) (* Should not happen unless oracle is very unprecise *)
            | `Value m -> m
          end
        | Struct s1, Struct s2 when are_structs_compatible s1 s2 ->
          let struct_value = S.unify aux s1.struct_value s2.struct_value in
          Struct { s1 with struct_value }
        | Struct s, Raw _ | Raw _, Struct s ->
          (* Previously implemented as weak_erase, it is useful to continue
             the recursive unification as there can be an emerging array segment
             in the sub structure. *)
          let v1 = to_struct ~oracle:(oracle Left) s.struct_type m1
          and v2 = to_struct ~oracle:(oracle Right) s.struct_type m2 in
          let struct_value = S.unify aux v1 v2 in
          Struct { s with struct_value }
        | Disjunct d1, Disjunct d2 when are_disjuncts_compatible d1 d2 ->
          let disj_value = D.unify ~oracle aux d1.disj_value d2.disj_value in
          Disjunct { d1 with disj_value }
        | Disjunct d, Raw _ | Raw _, Disjunct d ->
          let v1 = to_disj d.disj_type m1
          and v2 = to_disj d.disj_type m2 in
          let disj_value = D.unify ~oracle aux v1 v2 in
          Disjunct { d with disj_value }
        | Union u1, Union u2 when are_union_compatible u1 u2 ->
          Union {
            u1 with
            union_value = aux u1.union_value u2.union_value;
            union_padding = Bit.join u1.union_padding u2.union_padding;
          }
        | m, Raw b | Raw b, m -> weak_erase b m
        | _,_ -> Raw (Bit.join (raw m1) (raw m2))
      in
      aux

    let join ~oracle = unify ~oracle (fun ~size:_ -> V.join)

    let smash ~oracle = join ~oracle:(fun _ -> oracle)

    let read ~oracle (map : Cil_types.typ -> t -> 'a) (reduce : 'a -> 'a -> 'a) =
      let rec aux offset m =
        match offset, m with
        | NoOffset t, m ->
          map t m
        | Field (fi, offset'), Struct s
          when s.struct_type.ckey = fi.fcomp.ckey ->
          aux offset' (S.read s.struct_value fi)
        | Field (fi, offset'), Disjunct d
          when d.disj_type.ckey = fi.fcomp.ckey ->
          D.read (aux offset') reduce d.disj_value fi
        | Field (fi, offset'), Union u
          when Cil_datatype.Fieldinfo.equal u.union_field fi ->
          aux offset' u.union_value
        | Index (exp, index, elem_type, offset'), Array a
          when are_typ_compatible a.array_cell_type elem_type ->
          let open Top.Operators in
          let m =
            let+ lindex, uindex = match Option.map Bound.of_exp exp with
              | Some b -> `Value (b, b)
              | None | exception Bound.UnsupportedBoundExpression ->
                let l, u = Int_val.min_and_max index in
                let+ l = Top.of_option l
                and+ u = Top.of_option u in
                Bound.of_integer l, Bound.of_integer u
            in
            A.read ~oracle (aux offset') reduce a.array_value lindex uindex
          in
          begin match m with
            | `Value v -> v
            | `Top ->
              A.fold
                (fun m' acc -> reduce (aux offset' m') acc)
                (fun p () -> aux offset' (Raw p))
                a.array_value ()
          end
        | _, m -> (* structure mismatch *)
          let r = Raw (raw m) in
          match offset with
          | NoOffset t -> map t r
          | Field (_, offset') | Index (_, _, _, offset') -> aux offset' r
      in
      aux

    let update ~oracle (f : weak:bool -> Cil_types.typ -> t -> t or_bottom) =
      let open Bottom.Operators in
      let rec aux ~weak offset m =
        match offset with
        | NoOffset t ->
          f ~weak t m
        | Field (fi, offset') ->
          if fi.fcomp.cstruct then (* Structures *)
            if Config.disjunctive_invariants () then
              let old = to_disj fi.fcomp m in
              let+ disj_value = D.update ~oracle (aux ~weak offset') old fi in
              Disjunct { disj_type = fi.fcomp ; disj_value }
            else
              let old = to_struct ~oracle fi.fcomp m in
              let+ struct_value = S.update (aux ~weak offset') old fi in
              Struct { struct_type = fi.fcomp; struct_value }
          else (* Unions *)
            let old = match m with
              | Union u when Cil_datatype.Fieldinfo.equal u.union_field fi -> u
              | _ ->
                let b = raw m in
                { union_value = Raw b ; union_field = fi ; union_padding = b }
            in
            let+ union_value = aux ~weak offset' old.union_value in
            Union { old with union_value }
        | Index (exp, index, elem_type, offset') ->
          let m' =
            let open TopBottom.Operators in
            let* lindex, uindex, weak =
              match Option.map Bound.of_exp exp with
              | Some b -> `Value (b, Bound.succ b, weak)
              | None | exception Bound.UnsupportedBoundExpression ->
                begin match Int_val.min_and_max index with
                  | None, _ | _, None -> `Top
                  | Some l, Some u ->
                    let l' = Bound.of_integer l
                    and u' = Bound.(succ (of_integer u)) in
                    let weak =
                      weak ||
                      Option.is_some exp && not (Integer.equal l u)
                    in
                    `Value (l', u', weak)
                end
            in
            match m with
            | Array a when are_typ_compatible a.array_cell_type elem_type ->
              let+ array_value = A.update ~oracle (aux ~weak offset')
                  a.array_value lindex uindex in
              Array { a with array_value }
            | _ ->
              let b = raw m in
              let+ new_value = aux ~weak offset' (Raw b) in
              let array_value = A.single b lindex uindex new_value in
              Array { array_cell_type = elem_type ; array_value }
          in
          match m' with
          | `Top -> (* No suitable bound for the partition *)
            let+ v = f ~weak:true Cil.voidType m in v
          | `Bottom | `Value _ as m -> m
      in aux

    let incr_bound ~oracle vi x m = (* TODO: keep subtree when nothing changes *)
      let rec aux = function
        | (Raw _ | Scalar _) as m -> m
        | Struct s -> Struct { s with struct_value = S.map aux s.struct_value }
        | Disjunct d -> Disjunct { d with disj_value = D.map aux d.disj_value }
        | Union u -> Union { u with union_value = aux u.union_value }
        | Array a ->
          match  A.incr_bound ~oracle vi x a.array_value with
          | `Top -> Raw (A.raw a.array_value)
          | `Value array_value ->
            Array { a with array_value=A.map aux array_value }
      in
      aux m

    let add_segmentation_bounds ~oracle ~typ bounds =
      let convert_bound exp =
        try
          Some (Bound.of_exp exp)
        with Bound.UnsupportedBoundExpression -> None
      in
      let bounds = List.filter_map convert_bound bounds in
      function
      | (Raw b as m) ->
        begin match bounds with
          | l :: u :: t ->
            let array_value = A.single b l u m in
            let array_value = A.add_segmentation_bounds ~oracle t array_value in
            Array { array_cell_type = typ ; array_value }
          | _ -> m (* Can't build a segmentation with only one bound *)
        end
      | Array a ->
        let array_value = A.add_segmentation_bounds ~oracle bounds a.array_value
        in
        Array { a with array_value }
      | m -> m (* Ignore segmentation hints on non-array *)
  end
  and S : Abstract_structure.Structure with type submemory = ProtoMemory.t =
    Abstract_structure.Make (Config) (ProtoMemory)
  and A : Segmentation.Segmentation with type submemory = ProtoMemory.t =
    Segmentation.Make (Config) (ProtoMemory)
  and D : Abstract_structure.Disjunction with type submemory = ProtoMemory.t and type structure = S.t =
    Abstract_structure.Disjunction (ProtoMemory) (S)

  include ProtoMemory

  type location = Abstract_offset.t

  let pretty = pretty_root

  (* Constuctors *)

  let top = of_raw Bit.top
  let zero = of_raw Bit.zero
  let is_top m = m = top

  (* Widening *)

  let widen = unify

  (* Read/Write accesses *)

  let get ~oracle (m : t) (loc : location) : value =
    read ~oracle to_value V.join loc m

  let extract ~oracle (m : t) (loc : location) : t =
    read ~oracle (fun _typ x -> x) (smash ~oracle) loc m

  let update' ~oracle ~weak f offset m =
    let f' ~weak typ m =
      `Value (f ~weak typ m)
    in
    Bottom.non_bottom (update ~oracle ~weak f' offset m)

  let set ~oracle ~weak m offset new_v =
    let f ~weak typ m =
      of_value typ (if weak then V.join (to_value typ m) new_v else new_v)
    in
    update' ~oracle ~weak f offset m

  let reinforce ~oracle f m offset =
    let open Bottom.Operators in
    let f' ~weak typ m =
      if weak
      then `Value m
      else f (to_value typ m) >>-: of_value typ
    in
    update ~oracle ~weak:false f' offset m

  let erase ~oracle ~weak m offset b =
    let f ~weak _typ m =
      if weak then
        weak_erase b m
      else
        of_raw b
    in
    update' ~oracle ~weak f offset m

  let overwrite ~oracle ~weak dst offset src =
    let f ~weak _typ m =
      if weak then
        smash ~oracle m src
      else
        src
    in
    update' ~oracle ~weak f offset dst

  let segmentation_hint ~oracle m offset bounds =
    let f ~weak:_ typ m =
      add_segmentation_bounds ~oracle ~typ bounds m
    in
    update' ~oracle ~weak:false f offset m
end
