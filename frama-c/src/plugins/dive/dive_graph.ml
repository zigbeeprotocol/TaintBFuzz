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

let fresh_key =
  let next_key = ref 0 in
  fun () -> incr next_key; !next_key

let new_node
    ?(node_kind=Error "no kind")
    ?(node_locality={loc_file=""; loc_callstack=[]})
    () = {
  node_key = fresh_key ();
  node_kind;
  node_locality;
  node_is_root = false;
  node_hidden = false;
  node_values = None;
  node_range = Empty;
  node_writes_computation = NotDone;
  node_reads_computation = NotDone;
  node_writes_stmts = [];
}

module Node = Datatype.Make_with_collections
    (struct
      type t = node
      include Datatype.Serializable_undefined
      let name = "Dive.Node"
      let reprs = [ new_node () ]
      let compare n1 n2 = Datatype.Int.compare n1.node_key n2.node_key
      let hash n = n.node_key
      let equal n1 n2 = n1.node_key = n2.node_key
      let pretty fmt n = Format.pp_print_int fmt n.node_key
    end)

module Dependency =
struct
  type t = dependency
  let compare e1 e2 = e1.dependency_key - e2.dependency_key
  let hash e = e.dependency_key
  let equal e1 e2 = e1.dependency_key = e2.dependency_key
  let default = {
    dependency_key = -1;
    dependency_kind = Data;
    dependency_origins = []
  }
end

module G =
  Graph.Imperative.Digraph.ConcreteBidirectionalLabeled (Node) (Dependency)
include G


let create_node ~node_kind ~node_locality g =
  let node = new_node ~node_kind ~node_locality () in
  add_vertex g node;
  node

let remove_node = remove_vertex

let create_dependency g kinstr v1 dependency_kind v2 =
  let same_kind (_,e,_) =
    e.dependency_kind = dependency_kind
  in
  let matching_edge =
    try
      Some (List.find same_kind (G.find_all_edges g v1 v2))
    with Not_found -> None
  in
  let e = match matching_edge with
    | Some (_,e,_) -> e
    | None ->
      let e = {
        dependency_key = fresh_key ();
        dependency_kind;
        dependency_origins = []
      }
      in
      add_edge_e g (v1,e,v2);
      e
  in
  (* Add origins *)
  match kinstr with
  | Cil_types.Kglobal -> ()
  | Kstmt stmt ->
    let add_uniq l x =
      List.sort_uniq Cil_datatype.Stmt.compare (x :: l)
    in
    e.dependency_origins <- add_uniq e.dependency_origins stmt


let remove_dependency g edge =
  remove_edge_e g edge

let remove_dependencies g node =
  iter_pred_e (remove_dependency g) g node

let vertices g =
  fold_vertex (fun n acc -> n ::acc) g []

let edges g =
  fold_edges_e (fun d acc -> d ::acc) g []


let update_node_values node new_values typ =
  node.node_values <-
    Some (Extlib.opt_fold Cvalue.V.join node.node_values new_values);
  node.node_range <-
    Node_range.(upper_bound node.node_range (evaluate new_values typ))

let find_independant_nodes g roots =
  let module Dfs = Graph.Traverse.Dfs (struct
      include G
      (* Consider the graph as unoriented *)
      let iter_succ f g n =
        iter_pred f g n;
        iter_succ f g n

      let fold_succ f g n acc =
        let acc = fold_pred f g n acc in
        let acc = fold_succ f g n acc in
        acc
    end)
  in
  let module Table = Hashtbl.Make (Node) in
  let table = Table.create 13 in
  List.iter (Dfs.prefix_component (fun n -> Table.add table n true) g) roots;
  fold_vertex (fun n acc -> if Table.mem table n then acc else n :: acc) g []


let bfs ?(iter_succ=iter_succ) ?(limit=max_int) g roots =
  let module Table = Hashtbl.Make (Node) in
  let explored : int Table.t = Table.create 13
  and queue : (node * int) Queue.t = Queue.create () in
  (* Add roots to queue *)
  List.iter (fun root -> Queue.add (root,0) queue) roots;
  (* Iterate over the queue *)
  while not (Queue.is_empty queue) do
    let (n,d) = Queue.take queue in
    if d <= limit && not (Table.mem explored n) then begin
      Table.add explored n d;
      iter_succ (fun n' -> Queue.add (n',d+1) queue) g n
    end
  done;
  (* Convert the result to list *)
  Table.fold (fun n _ l -> n :: l) explored []


let ouptput_to_dot out_channel g =
  let open Graph.Graphviz.DotAttributes in
  (* let g = add_dummy_nodes g in *)

  let build_label s = `HtmlLabel (Extlib.html_escape s) in

  let module FileTable = Datatype.String.Hashtbl in
  let module CallstackTable = Value_types.Callstack.Hashtbl in
  let file_table = FileTable.create 13
  and callstack_table = CallstackTable.create 13 in
  let file_counter = ref 0 in
  let callstack_counter = ref 0 in
  let rec build_file_subgraph filename =
    incr file_counter;
    {
      sg_name = "file_" ^ (string_of_int !file_counter);
      sg_attributes = [build_label filename];
      sg_parent = None;
    }
  and build_callstack_subgraph = function
    | [] -> None
    | (kf,_kinstr) :: stack ->
      let parent = get_callstack_subgraph stack in
      incr callstack_counter;
      Some {
        sg_name = "cs_" ^ (string_of_int !callstack_counter);
        sg_attributes = [build_label (Kernel_function.get_name kf)];
        sg_parent = Option.map (fun sg -> sg.sg_name) parent;
      }
  and get_file_subgraph filename =
    FileTable.memo file_table filename build_file_subgraph
  and get_callstack_subgraph cs =
    CallstackTable.memo callstack_table cs build_callstack_subgraph
  in

  let module Dot = Graph.Graphviz.Dot (
    struct
      include G
      let graph_attributes _g = []
      let default_vertex_attributes _g = []
      let vertex_name v = "cp" ^ (string_of_int v.node_key)
      let vertex_attributes v =
        let l = ref [] in
        let text = Pretty_utils.to_string Node_kind.pretty v.node_kind in
        if text <> "" then
          l := build_label text :: !l;
        let kind = match v.node_kind with
          | Scalar _ -> [`Shape `Box]
          | Composite _ -> [ `Shape `Box3d ]
          | Scattered _ -> [ `Shape `Parallelogram ]
          | Unknown _ -> [`Shape `Diamond ; `Color 0xff0000]
          | Alarm _ ->  [ `Shape `Doubleoctagon ;
                          `Style `Bold ; `Color 0xff0000 ;
                          `Style `Filled ; `Fillcolor 0xff0000 ]
          | AbsoluteMemory | String _ -> [`Shape `Box3d]
          | Error _ -> [`Color 0xff0000]
        and range = match v.node_range with
          | Empty -> []
          | Singleton ->
            [`Color 0x88aaff ; `Style `Filled ; `Fillcolor 0xaaccff ]
          | Normal _ ->
            [ `Color 0x004400 ; `Style `Filled ; `Fillcolor 0xeeffee ]
          | Wide ->
            [ `Color 0xff0000 ; `Style `Filled ; `Fillcolor 0xffbbbb ]
        in
        l := range @ kind @ !l;
        if v.node_writes_computation <> Done then
          l := [ `Style `Dotted ] @ !l;
        if v.node_is_root then
          l := [ `Style `Bold ] @ !l;
        !l
      let get_subgraph v =
        let {loc_file ; loc_callstack} = v.node_locality in
        match loc_callstack with
        | [] -> Some (get_file_subgraph loc_file)
        | cs -> get_callstack_subgraph cs
      let default_edge_attributes _g = []
      let edge_attributes (_v1,e,_v2) =
        let kind_attribute = match e.dependency_kind with
          | Callee -> [`Color 0x00ff00 ]
          | _ -> []
        and folding_attribute = match e.dependency_origins with
          | [] | [_] -> []
          | _ -> [ `Style `Bold ]
        in kind_attribute @ folding_attribute
    end)
  in
  Dot.output_graph out_channel g

module JsonPrinter =
struct
  let output_stmt stmt =
    let kf = Kernel_function.find_englobing_kf stmt in
    Server.Kernel_ast.KfMarker.to_json (kf, PStmtStart (kf, stmt))

  let output_kinstr = function
    | Cil_types.Kglobal -> `String "global"
    | Cil_types.Kstmt stmt -> `Int stmt.Cil_types.sid

  let output_callsite (kf,kinstr) =
    `Assoc [
      ("fun", `String (Kernel_function.get_name kf)) ;
      ("instr", output_kinstr kinstr) ;
    ]

  let output_callstack cs =
    `List (List.map output_callsite cs)

  let output_node_kind kind =
    let s = match kind with
      | Scalar _ -> "scalar"
      | Composite _ -> "composite"
      | Scattered _ -> "scattered"
      | Unknown _ -> "unknown"
      | Alarm _ -> "alarm"
      | AbsoluteMemory -> "absolute"
      | String _ -> "string"
      | Error _ -> "error"
    in
    `String s

  let output_node_locality { loc_file ; loc_callstack } =
    let f1 = ("file", `String loc_file) in
    let fields = match loc_callstack with
      | [] -> [f1]
      | cs -> [f1 ; ("callstack", output_callstack cs)]
    in
    `Assoc fields

  let output_range range =
    match range with
    | Empty -> `String "empty"
    | Singleton -> `String "singleton"
    | Normal range_grade -> `Int range_grade
    | Wide -> `String "wide"

  let output_dep_kind kind =
    let s = match kind with
      | Callee -> "callee"
      | Data -> "data"
      | Address -> "addr"
      | Control -> "ctrl"
      | Composition -> "comp"
    in
    `String s

  let output_node_values values =
    match values with
    | None -> `Null
    | Some cvalue when Cvalue.V.is_bottom cvalue -> `Null
    | Some cvalue -> `String (Pretty_utils.to_string Cvalue.V.pretty cvalue)

  let output_computation = function
    | Done -> `String "yes"
    | Partial _ -> `String "partial"
    | NotDone -> `String "no"

  let output_node node =
    let label = Pretty_utils.to_string Node_kind.pretty node.node_kind in
    `Assoc ([
        ("id", `Int node.node_key) ;
        ("label", `String label) ;
        ("kind", output_node_kind node.node_kind) ;
        ("locality", output_node_locality node.node_locality) ;
        ("is_root", `Bool node.node_is_root) ;
        ("backward_explored", output_computation node.node_writes_computation) ;
        ("forward_explored", output_computation node.node_reads_computation) ;
        ("writes", `List (List.map output_stmt node.node_writes_stmts)) ;
        ("values",  output_node_values node.node_values) ;
        ("range",  output_range node.node_range) ;
      ] @
        begin match Node_kind.to_lval node.node_kind with
          | None -> []
          | Some lval ->
            let typ = Cil.typeOfLval lval in
            let str = Pretty_utils.to_string Cil_printer.pp_typ typ in
            [("type", `String str)]
        end)

  let output_dep (n1,dep,n2) =
    `Assoc [
      ("id", `Int dep.dependency_key) ;
      ("src", `Int n1.node_key) ;
      ("dst", `Int n2.node_key) ;
      ("kind", output_dep_kind dep.dependency_kind) ;
      ("origins", `List (List.map output_stmt dep.dependency_origins)) ;
    ]

  let output_graph g =
    `Assoc [
      ("nodes", `List (List.map output_node (vertices g))) ;
      ("deps", `List (List.map output_dep (edges g)))
    ]

  let output_diff g diff =
    let root = match diff.last_root with
      | None -> `Null
      | Some root -> `Int root.node_key
    and added_nodes = List.map output_node diff.added_nodes
    and added_deps =
      let module Set = Set.Make (struct
          type t = edge
          let compare (_,d1,_) (_,d2,_) = d1.dependency_key - d2.dependency_key
        end)
      in
      let collect_deps set node =
        let set = fold_pred_e Set.add g node set in
        let set = fold_succ_e Set.add g node set in
        set
      in
      let set = List.fold_left collect_deps Set.empty diff.added_nodes in
      List.map output_dep (Set.elements set)
    and removed_nodes =
      List.map (fun node -> `Int node.node_key) diff.removed_nodes
    in
    `Assoc [
      ("root", root) ;
      ("add", `Assoc [
          ("nodes", `List added_nodes) ;
          ("deps", `List added_deps)
        ]) ;
      ("sub", `List removed_nodes)]
end

let ouptput_to_json out_channel g =
  let json = JsonPrinter.output_graph g in
  Yojson.Basic.to_channel out_channel json

let to_json g =
  JsonPrinter.output_graph g

let diff_to_json g diff =
  JsonPrinter.output_diff g diff
