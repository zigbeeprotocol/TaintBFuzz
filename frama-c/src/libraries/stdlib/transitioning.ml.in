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

(* Generated file. The file to update is [transitioning.ml.in] *)

module List = struct

  let concat_map f l =
    let rec aux f acc = function
      | [] -> List.rev acc
      | x :: l ->
        let xs = f x in
        aux f (List.rev_append xs acc) l
    in aux f [] l

  let equal f l1 l2 =
    l1 == l2 || try List.for_all2 f l1 l2 with Invalid_argument _ -> false

  let rec compare f l1 l2 =
    if l1 == l2 then 0
    else match l1, l2 with
      | [], [] -> assert false
      | [], _ :: _ -> -1
      | _ :: _, [] -> 1
      | x1 :: q1, x2 :: q2 ->
        let n = f x1 x2 in
        if n = 0 then compare f q1 q2 else n
end
