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

module Graph = Dive_graph

let dkey = Self.register_category "context"


module NodeRef = Datatype.Pair_with_collections
    (Node_kind) (Callstack)
    (struct let module_name = "Build.NodeRef" end)

module Index = Datatype.Int.Hashtbl
module NodeTable = FCHashtbl.Make (NodeRef)
module NodeSet = Graph.Node.Set
module BaseSet = Cil_datatype.Varinfo.Set

type t = {
  mutable graph: Graph.t;
  mutable vertex_table: node Index.t; (* node_key -> node *)
  mutable node_table: node NodeTable.t; (* node_kind * callstack -> node *)
  mutable unfolded_bases: BaseSet.t;
  mutable hidden_bases: BaseSet.t;
  mutable max_dep_fetch_count: int;
  mutable roots: NodeSet.t;
  mutable graph_diff: graph_diff;
}


(* --- initialization --- *)

let create () =
  Eva.Analysis.compute ();
  {
    graph = Graph.create ();
    vertex_table = Index.create 13;
    node_table = NodeTable.create 13;
    unfolded_bases = BaseSet.empty;
    hidden_bases = BaseSet.empty;
    max_dep_fetch_count = 10;
    roots = NodeSet.empty;
    graph_diff = { last_root = None ; added_nodes=[] ; removed_nodes=[] };
  }

let clear context =
  context.graph <- Graph.create ();
  context.vertex_table <- Index.create 13;
  context.node_table <- NodeTable.create 13;
  context.max_dep_fetch_count <- 10;
  context.roots <- NodeSet.empty;
  context.graph_diff <- { last_root = None ; added_nodes=[] ; removed_nodes=[] }


(* --- Accessors --- *)

let get_graph context =
  context.graph

let find_node context node_key =
  Index.find context.vertex_table node_key

let get_max_dep_fetch_count context =
  context.max_dep_fetch_count


(* --- State --- *)

let is_node_updated context node =
  let is_node n = Graph.Node.equal node n in
  List.exists is_node context.graph_diff.removed_nodes ||
  List.exists is_node context.graph_diff.added_nodes

let update_diff context node =
  if not (is_node_updated context node) then
    context.graph_diff <- {
      context.graph_diff with
      added_nodes = node :: context.graph_diff.added_nodes;
    }

let take_last_diff context =
  let pp_node fmt n = Format.pp_print_int fmt n.node_key in
  let pp_node_list = Pretty_utils.pp_list ~sep:",@, " pp_node in
  let diff = context.graph_diff in
  Self.debug ~dkey "root: %a,@, added: %a,@, subbed: %a"
    (Pretty_utils.pp_opt pp_node) diff.last_root
    pp_node_list diff.added_nodes
    pp_node_list diff.removed_nodes;
  context.graph_diff <- {
    last_root = None ;
    added_nodes=[] ;
    removed_nodes=[]
  };
  diff


(* --- Roots --- *)

let get_roots context =
  NodeSet.elements context.roots

let update_roots context new_roots =
  let old_roots = context.roots in
  context.roots <- new_roots;
  let unset n =
    if not (NodeSet.mem n new_roots) then begin
      n.node_is_root <- false;
      update_diff context n
    end
  and set n =
    if not (NodeSet.mem n old_roots) then begin
      n.node_is_root <- true;
      update_diff context n
    end
  in
  NodeSet.iter unset old_roots;
  NodeSet.iter set new_roots

let set_unique_root context root =
  update_roots context (NodeSet.singleton root)

let add_root context root =
  update_roots context (NodeSet.add root context.roots)

let remove_root context root =
  update_roots context (NodeSet.remove root context.roots)


(* --- Folding --- *)

let is_folded context vi =
  not (BaseSet.mem vi context.unfolded_bases)

let fold context vi =
  context.unfolded_bases <- BaseSet.remove vi context.unfolded_bases

let unfold context vi =
  context.unfolded_bases <- BaseSet.add vi context.unfolded_bases


(* --- Base hiding --- *)

let is_hidden context node_kind =
  match Node_kind.get_base node_kind with
  | Some vi when BaseSet.mem vi context.hidden_bases -> true
  | _ -> false

let show context vi =
  context.hidden_bases <- BaseSet.add vi context.hidden_bases

let hide context vi =
  context.hidden_bases <- BaseSet.add vi context.hidden_bases


(* --- Building --- *)

let add_node context ~node_kind ~node_locality =
  let node_ref = (node_kind, node_locality.loc_callstack) in
  let add_new _ =
    let node = Graph.create_node context.graph ~node_kind ~node_locality in
    node.node_hidden <- is_hidden context node.node_kind;
    Index.add context.vertex_table node.node_key node;
    update_diff context node;
    node
  in
  NodeTable.memo context.node_table node_ref add_new

let remove_node context node =
  let node_ref = (node.node_kind, node.node_locality.loc_callstack) in
  let graph = context.graph in
  Graph.iter_succ (fun n -> n.node_writes_computation <- NotDone) graph node;
  Graph.iter_pred (fun n -> n.node_reads_computation <- NotDone) graph node;
  Graph.remove_node context.graph node;
  Index.remove context.vertex_table node.node_key;
  NodeTable.remove context.node_table node_ref;
  let is_not_node n = not (Graph.Node.equal node n) in
  context.graph_diff <- {
    context.graph_diff with
    added_nodes = List.filter is_not_node context.graph_diff.added_nodes;
    removed_nodes = node :: context.graph_diff.removed_nodes;
  }
