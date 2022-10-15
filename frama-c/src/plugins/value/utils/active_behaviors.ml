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

open Cil_types

let create_conjunction l =
  let open Logic_const in
  let loc = match l with
    | [] -> None
    | p :: _ -> Some (pred_of_id_pred p).pred_loc
  in
  let predicates = List.map pred_of_id_pred l in
  List.fold_right (fun p1 p2 -> pand ?loc (p1, p2)) predicates ptrue

type t = {
  funspec: funspec;
  is_active: funbehavior -> Alarmset.status
}

module HashBehaviors = Hashtbl.Make(
  struct
    type t = funbehavior
    let equal b1 b2 = b1.b_name = b2.b_name
    let hash b = Hashtbl.hash b.b_name
  end)

let is_active eval_predicate b =
  let assumes = create_conjunction b.b_assumes in
  eval_predicate assumes

let create eval_predicate funspec =
  let h = HashBehaviors.create 3 in
  let is_active = fun b ->
    try HashBehaviors.find h b
    with Not_found ->
      let active = is_active eval_predicate b in
      HashBehaviors.add h b active;
      active
  in
  { is_active; funspec }

let is_active ab behavior = ab.is_active behavior

let active_behaviors ab =
  List.filter
    (fun b -> is_active ab b != Alarmset.False)
    ab.funspec.spec_behavior

let is_active_from_name ab name =
  try
    let list = ab.funspec.spec_behavior in
    let behavior = List.find (fun b' -> b'.b_name = name) list in
    is_active ab behavior
  (* This case happens for behaviors of statement contract, that are not
     handled by this module. *)
  with Not_found -> Alarmset.Unknown
