(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) Jean-Christophe Filliatre                               *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2, with the special exception on linking              *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(* Modified by CEA *)

open Obj

(* Pointers already visited are stored in a hash-table, where
    comparisons are done using physical equality. *)

external address_of_value: 'a -> int = "address_of_value"

module H = Hashtbl.Make(
  struct 
    type t = Obj.t 
    let equal = (==) 
    let hash = address_of_value
  end)

let node_table = (H.create 257 : unit H.t)

(* Addresses that will be skipped *)
let except_table = (H.create 257 : unit H.t)

let in_table o = H.mem node_table o || H.mem except_table o

let add_in_table o = H.add node_table o ()

let mark_as_skipped () =
  H.iter (fun addr () -> H.add except_table addr ()) node_table

let reset_table () = H.clear node_table

(*s Objects are traversed recursively, as soon as their tags are less than
    [no_scan_tag]. [count] records the numbers of words already visited. *)

let size_of_double = size (repr 1.0)

let count = ref 0

let rec traverse t =
  if not (in_table t) then begin
    add_in_table t;
    if is_block t then begin
      let n = size t in
      let tag = tag t in
      if tag < no_scan_tag then begin
	count := !count + 1 + n;
	for i = 0 to n - 1 do
      	  let f = field t i in 
	  if is_block f then traverse f
	done
      end else if tag = string_tag then
	count := !count + 1 + n 
      else if tag = double_tag then
	count := !count + size_of_double
      else if tag = double_array_tag then
	count := !count + 1 + size_of_double * n 
      else
	incr count
    end
  end

let res () =
  let r = !count in
  reset_table ();
  count := 0;
  r

(* CEA *)

let all_sizes () =
  Gc.compact ();
  Gc.set { (Gc.get ()) with
           Gc.max_overhead = 1000000; allocation_policy = 1 } (* disable compaction *);
  let states =
    State_builder.States.fold (fun name _ v _ acc -> (name, Obj.repr v) :: acc) []
  in
  let ast = List.assoc "AST" states in
  let add acc name =
    let size : int = (res ()) / 1000 in
    if size <> 0 then (size, name) :: acc else acc
  in
  (* Compute the size of the AST, and mark the entire AST as skipped *)
  traverse ast;
  mark_as_skipped ();
  let res = add [] "AST" in
  (* Now traverse the other states, but implicitly excluding the AST *)
  let aux acc (state, v) =
    traverse v;
    add acc state
  in
  let res = List.fold_left aux res states in
  (* Sort by increasing size *)
  let res = List.sort (fun (s1, _) (s2, _) -> compare s1 s2) res in
  let pp fmt (size, name) = Format.fprintf fmt "@[%d kW, %s@]" size name in
  Kernel.result "## Sizes ##@.%a"
    (Pretty_utils.pp_list ~pre:"@[<v>" ~suf:"@]" ~sep:"@ " pp) res
    
let () = Db.Main.extend all_sizes
