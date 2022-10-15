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

open Dive_types

module DatatypeInput =
struct
  include Datatype.Undefined

  open Cil_datatype

  type t = node_kind

  let (<?>) c (cmp,x,y) =
    if c = 0
    then cmp x y
    else c

  let name = "Node_kind"

  let reprs = [ Scalar (
      List.hd Varinfo.reprs,
      List.hd Typ.reprs,
      List.hd Offset.reprs) ]

  let compare k1 k2 =
    match k1, k2 with
    | Scalar (vi1, _, offset1), Scalar (vi2, _, offset2) ->
      Varinfo.compare vi1 vi2 <?> (OffsetStructEq.compare, offset1, offset2)
    | Scalar _, _ -> 1
    | _, Scalar _ -> -1
    | Composite vi1, Composite vi2 -> Varinfo.compare vi1 vi2
    | Composite _, _ -> 1
    | _, Composite _ -> -1
    | Scattered (lv1,ki1), Scattered (lv2,ki2) ->
      LvalStructEq.compare lv1 lv2 <?> (Kinstr.compare, ki1, ki2)
    | Scattered _, _ -> 1
    | _, Scattered _ -> -1
    | Unknown (lv1,ki1), Unknown (lv2,ki2) ->
      LvalStructEq.compare lv1 lv2 <?> (Kinstr.compare, ki1, ki2)
    | Unknown _, _ -> 1
    | _, Unknown _ -> -1
    | Alarm (stmt1, alarm1), Alarm (stmt2, alarm2) ->
      Stmt.compare stmt1 stmt2 <?> (Alarms.compare, alarm1, alarm2)
    | Alarm _, _ -> 1
    | _, Alarm _ -> -1
    | AbsoluteMemory, AbsoluteMemory -> 0
    | AbsoluteMemory, _ -> 1
    | _, AbsoluteMemory -> -1
    | String (i1,_), String (i2,_) ->
      Datatype.Int.compare i1 i2
    | String _, _ -> 1
    | _, String _ -> -1
    | Error s1, Error s2 ->
      Datatype.String.compare s1 s2

  let equal k1 k2 =
    match k1, k2 with
    | Scalar (vi1, _, offset1), Scalar (vi2, _, offset2) ->
      Varinfo.equal vi1 vi2 && OffsetStructEq.equal offset1 offset2
    | Composite vi1, Composite vi2 -> Varinfo.equal vi1 vi2
    | Scattered (lv1, ki1), Scattered (lv2, ki2) ->
      LvalStructEq.equal lv1 lv2 && Kinstr.equal ki1 ki2
    | Unknown (lv1, ki1), Unknown (lv2, ki2) ->
      LvalStructEq.equal lv1 lv2 && Kinstr.equal ki1 ki2
    | Alarm (stmt1, alarm1), Alarm (stmt2, alarm2) ->
      Stmt.equal stmt1 stmt2 && Alarms.equal alarm1 alarm2
    | AbsoluteMemory, AbsoluteMemory -> true
    | String (i,_), String (j,_) -> Datatype.Int.equal i j
    | Error s1, Error s2 -> Datatype.String.equal s1 s2
    | _ -> false

  let hash k =
    match k with
    | Scalar (vi, _, offset) ->
      Hashtbl.hash (1, Varinfo.hash vi, OffsetStructEq.hash offset)
    | Composite vi -> Hashtbl.hash (2, Varinfo.hash vi)
    | Scattered (lv, ki) ->
      Hashtbl.hash (3, LvalStructEq.hash lv, Kinstr.hash ki)
    | Unknown (lv, ki) ->
      Hashtbl.hash (4, LvalStructEq.hash lv, Kinstr.hash ki)
    | Alarm (stmt, alarm) ->
      Hashtbl.hash (5, Stmt.hash stmt, Alarms.hash alarm)
    | AbsoluteMemory -> 6
    | String (i, _) -> Hashtbl.hash (7, i)
    | Error s -> Hashtbl.hash (8, s)
end

include Datatype.Make (DatatypeInput)


let get_base = function
  | Scalar (vi,_,_) | Composite (vi) -> Some vi
  | Scattered _ | Unknown _ | Alarm _ | AbsoluteMemory | String _ | Error _ ->
    None

let to_lval = function
  | Scalar (vi,_typ,offset) -> Some (Cil_types.Var vi, offset)
  | Composite (vi) -> Some (Cil_types.Var vi, Cil_types.NoOffset)
  | Scattered (lval,_) -> Some lval
  | Unknown (lval,_) -> Some lval
  | Alarm (_,_) | AbsoluteMemory | String _ | Error _ -> None

let pretty fmt = function
  | (Scalar _ | Composite _ | Scattered _ | Unknown _) as kind ->
    Cil_printer.pp_lval fmt (Option.get (to_lval kind))
  | Alarm (_stmt,alarm) ->
    Cil_printer.pp_predicate fmt (Alarms.create_predicate alarm)
  | AbsoluteMemory ->
    Format.fprintf fmt "%s" (Kernel.AbsoluteValidRange.get ())
  | String (_, CSString s) ->
    Format.fprintf fmt "%S" s
  | String (_, CSWstring s) ->
    Format.fprintf fmt "L\"%s\"" (Escape.escape_wstring s)
  | Error s ->
    Format.fprintf fmt "%s" s
