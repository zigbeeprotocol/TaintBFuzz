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

include Value_types.Callstack

type call_site = Value_types.call_site
module Callsite = Value_types.Callsite

let init kf = [(kf,Kglobal)]

let pop cs =
  match cs with
  | [] | (_,Kglobal) :: _ :: _ | [(_,Kstmt _)] -> assert false (* Invariant *)
  | [(_,Kglobal)] -> None
  | (kf,Kstmt stmt) :: t -> Some (kf,stmt,t)

let top_kf cs =
  match cs with
  | [] | (_,Kglobal) :: _ :: _ | [(_,Kstmt _)] -> assert false (* Invariant *)
  | (kf,_) :: _ -> kf

let rec pop_downto top_kf = function
  | [] -> failwith "the callstack doesn't contain this function"
  | ((kf,_kinstr) :: tail) as cs ->
    if Kernel_function.equal kf top_kf
    then cs
    else pop_downto top_kf tail

let push (kf,stmt) cs =
  match cs with
  (* When the callstack is truncated, we ignore the first callsite *)
  | [] -> [(kf,Kglobal)]
  | cs -> (kf,Kstmt stmt) :: cs

let rec is_prefix cs1 cs2 =
  match cs1, cs2 with
  | [], _ -> true
  | _, [] -> false
  | [(kf,Kglobal)], (kf',_)::_ -> Kernel_function.equal kf kf'
  | _, [(_,Kglobal)] -> false
  | s1 :: t1, s2 :: t2 ->
    if Callsite.equal s1 s2
    then is_prefix t1 t2
    else false

let truncate_to_sub full_cs sub_cs =
  let rec aux acc = function
    | [] -> None
    | (s :: t) as cs ->
      if is_prefix sub_cs cs
      then Some (List.rev acc @ sub_cs)
      else aux (s :: acc) t
  in
  aux [] full_cs

let list_filter_map f l =
  let aux acc x =
    match f x with
    | None -> acc
    | Some y -> y :: acc
  in
  List.rev (List.fold_left aux [] l)

let filter_truncate l sub_cs =
  list_filter_map (fun cs -> truncate_to_sub cs sub_cs) l
