(**************************************************************************)
(*                                                                        *)
(*  This file is part of Aorai plug-in of Frama-C.                        *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*    INRIA (Institut National de Recherche en Informatique et en         *)
(*           Automatique)                                                 *)
(*    INSA  (Institut National des Sciences Appliquees)                   *)
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

open Promelaast

type state = Promelaast.state
type transition = Promelaast.typed_trans

module Vertex =
struct
  type t = state
  let compare x y = Stdlib.compare x.nums y.nums
  let hash x = Hashtbl.hash x.nums
  let equal x y = x.nums = y.nums
  let default = {
    nums = -1; name = ""; multi_state = None;
    acceptation = Bool3.False; init = Bool3.False
  }
end

module Edge =
struct
  type t = transition
  let compare x y = Stdlib.compare x.numt y.numt
  let default = {
    numt = -1; start = Vertex.default; stop = Vertex.default;
    cross = TTrue; actions = []
  }
end

include Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (Vertex) (Edge)

let of_automaton auto =
  let g = create () in
  List.iter (fun t -> add_edge_e g (t.start,t,t.stop)) auto.trans;
  g

let states g =
  fold_vertex (fun v acc -> v :: acc) g []

let filter_states f g =
  fold_vertex (fun v acc -> if f v then v :: acc else acc) g []

let init_states g =
  filter_states (fun v -> v.Promelaast.init = Bool3.True) g

let edges g =
  fold_edges_e (fun e acc -> e :: acc) g []
