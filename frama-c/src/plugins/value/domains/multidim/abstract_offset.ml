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
open Top.Operators

type t =
  | NoOffset of Cil_types.typ
  | Index of Cil_types.exp option * Int_val.t * Cil_types.typ * t
  | Field of Cil_types.fieldinfo * t

let rec pretty fmt = function
  | NoOffset _t -> ()
  | Field (fi, s) -> Format.fprintf fmt ".%s%a" fi.fname pretty s
  | Index (None, i, _t, s) ->
    Format.fprintf fmt "[%a]%a"
      Int_val.pretty i
      pretty s
  | Index (Some e, i, _t, s) ->
    Format.fprintf fmt "[%a∈%a]%a"
      Cil_printer.pp_exp e
      Int_val.pretty i
      pretty s

let rec append o1 o2 =
  match o1 with
  | NoOffset _t -> o2
  | Field (fi, s) -> Field (fi, append s o2)
  | Index (e, i, t, s) -> Index (e, i, t, append s o2)

let add_index oracle base exp =
  let rec aux = function
    | NoOffset _ as o ->
      let idx = oracle exp in
      if Int_val.is_zero idx
      then `Value o
      else `Top (* Can't add index if not an array *)
    | Field (fi, sub) ->
      let+ sub' = aux sub in
      Field (fi, sub')
    | Index (e, i, t, (NoOffset _ as sub)) ->
      let idx' = Int_val.add i (oracle exp) in
      let loc = Cil_datatype.Location.unknown in
      let e = match e with (* If i is singleton, we can use this as the index expression *)
        | None when Int_val.is_singleton i ->
          let loc = Cil_datatype.Location.unknown in
          Some (Cil.kinteger64 ~loc (Int_val.project_int i))
        | e -> e
      in
      let e' = Option.map (Fun.flip (Cil.mkBinOp ~loc Cil_types.PlusA) exp) e in
      (* TODO: is idx inside bounds ? *)
      `Value (Index (e', idx', t, sub))
    | Index (e, i, t, sub) ->
      let+ sub' = aux sub in
      Index (e, i, t, sub')
  in
  aux base

let rec join o1 o2 =
  match o1, o2 with
  | NoOffset t, NoOffset t'
    when Bit_utils.type_compatible t t' ->
    `Value (NoOffset t)
  | Field (fi, sub1), Field (fi', sub2)
    when Cil_datatype.Fieldinfo.equal fi fi' ->
    let+ sub' = join sub1 sub2 in
    Field (fi, sub')
  | Index (e1, i1, t, sub1), Index (e2, i2, t', sub2)
    when Bit_utils.type_compatible t t' ->
    let e = match e1, e2 with
      | Some e1, Some e2 when Cil_datatype.ExpStructEq.equal e1 e2 ->
        Some e1 (* keep expression only when equivalent from both offsets *)
      | _ -> None
    in
    let+ sub' = join sub1 sub2 in
    Index (e, Int_val.join i1 i2, t, sub')
  | _ -> `Top

let array_bounds array_size =
  (* TODO: handle undefined sizes and not const foldable sizes *)
  match array_size with
  | None -> None
  | Some size_exp ->
    match Cil.constFoldToInt size_exp with
    | None -> None
    | Some size when Integer.(gt size zero) -> Some Integer.(zero, pred size)
    | Some _ -> None

let array_range array_size =
  Option.map
    (fun (l,u) -> Int_val.inject_range (Some l) (Some u))
    (array_bounds array_size)

let assert_valid_index idx size =
  match array_range size with
  | Some range when Int_val.is_included idx range -> `Value ()
  | _ -> `Top

let of_var_address vi =
  NoOffset vi.Cil_types.vtype

let rec of_cil_offset oracle base_typ = function
  | Cil_types.NoOffset -> `Value (NoOffset base_typ)
  | Field (fi, sub) ->
    if Cil.typeHasQualifier "volatile" fi.ftype then
      `Top
    else
      let+ sub' = of_cil_offset oracle fi.ftype sub in
      Field (fi, sub')
  | Index (exp, sub) ->
    match Cil.unrollType base_typ with
    | TArray (elem_typ, array_size, _) ->
      let idx = oracle exp in
      let+ () = assert_valid_index idx array_size
      and+ sub' = of_cil_offset oracle elem_typ sub in
      Index (Some exp, idx, elem_typ, sub')
    | _ -> assert false

let rec of_int_val ~base_typ ~typ ival =
  if Int_val.is_zero ival && Bit_utils.type_compatible base_typ typ then
    `Value (NoOffset typ)
  else
    match Cil.unrollType base_typ with
    | TArray (elem_typ, array_size, _) ->
      let* range, rem =
        try
          let elem_size = Integer.of_int (Cil.bitsSizeOf elem_typ) in
          if Integer.is_zero elem_size then (* array of elements of size 0 *)
            if Int_val.is_zero ival then (* the whole range is valid *)
              let+ range = Top.of_option (array_range array_size) in
              range, ival
            else (* Non-zero offset cannot represent anything here *)
              `Top
          else
            let range = Int_val.scale_div ~pos:true elem_size ival
            and rem = Int_val.scale_rem ~pos:true elem_size ival in
            `Value (range, rem)
        with Cil.SizeOfError (_,_) ->
          (* Cil.bitsSizeOf can raise an exception when elements are
              themselves array of execution-time size *)
          if Int_val.is_zero ival then
            `Value (ival, ival)
          else
            `Top
      in
      let+ () = assert_valid_index range array_size
      and+ sub' = of_int_val ~base_typ:elem_typ ~typ rem in
      Index (None, range, elem_typ, sub')

    | TComp (ci, _) ->
      if not ci.cstruct then
        (* Ignore unions for now *)
        `Top
      else
        let rec find_field = function
          | [] -> `Top
          | fi :: q ->
            let offset, width = Cil.fieldBitsOffset fi in
            let l = Integer.(of_int offset) in
            let u = Integer.(pred (add l (of_int width))) in
            let matches =
              if width = 0 then
                Int_val.(equal ival (inject_singleton l))
              else
                let range = Int_val.inject_range (Some l) (Some u) in
                Int_val.is_included ival range
            in
            if matches then
              if Cil.typeHasQualifier "volatile" fi.ftype then
                `Top
              else
                let sub_ival = Int_val.add_singleton (Integer.neg l) ival in
                let+ sub' = of_int_val ~base_typ:fi.ftype ~typ sub_ival in
                Field (fi, sub')
            else
              find_field q
        in
        find_field (Option.value ~default:[] ci.cfields)

    | _ -> `Top

let of_ival ~base_typ ~typ ival =
  match Ival.project_int_val ival with
  | Some ival -> of_int_val ~base_typ ~typ ival
  | None -> `Top

let index_of_term array_size t = (* Exact constant ranges *)
  match t.Cil_types.term_node with
  | TConst (Integer (v, _)) -> `Value (Int_val.inject_singleton v)
  | Trange (l,u) ->
    let eval bound = function
      | None -> Top.of_option bound
      | Some { Cil_types.term_node=TConst (Integer (v, _)) } -> `Value v
      | Some _ -> `Top
    in
    let bounds = array_bounds array_size in
    let lb = Option.map fst bounds and ub = Option.map snd bounds in
    let+ l' = eval lb l and+ u' = eval ub u in
    Int_val.inject_range (Some l') (Some u')
  | _ -> `Top

let rec of_term_offset base_typ = function
  | Cil_types.TNoOffset -> `Value (NoOffset base_typ)
  | TField (fi, sub) ->
    if Cil.typeHasQualifier "volatile" fi.ftype then
      `Top
    else
      let+ sub' = of_term_offset fi.ftype sub in
      Field (fi, sub')
  | TIndex (index, sub) ->
    begin match Cil.unrollType base_typ with
      | TArray (elem_typ, array_size, _) ->
        let* idx = index_of_term array_size index in
        let+ () = assert_valid_index idx array_size
        and+ sub' = of_term_offset elem_typ sub in
        Index (None, idx, elem_typ, sub')
      | _ -> assert false
    end
  | _ -> `Top

let rec is_singleton = function
  | NoOffset _ -> true
  | Field (_fi, sub) -> is_singleton sub
  | Index (e, ival, _elem_typ, sub) ->
    (Option.is_some e || Int_val.is_singleton ival) && is_singleton sub

let references =
  let rec aux acc = function
    | NoOffset _ -> acc
    | Field (_, sub) | Index (None, _, _, sub) -> aux acc sub
    | Index (Some e, _, _, sub) ->
      let r = Cil.extract_varinfos_from_exp e in
      let acc = Cil_datatype.Varinfo.Set.union r acc in
      aux acc sub
  in
  aux Cil_datatype.Varinfo.Set.empty
