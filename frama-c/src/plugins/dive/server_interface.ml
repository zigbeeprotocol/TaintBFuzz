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

open Server
open Data
open Dive_types

let package = Package.package ~plugin:"dive" ~title:"Dive Services" ()


(* -------------------------------------------------------------------------- *)
(* --- State handling                                                     --- *)
(* -------------------------------------------------------------------------- *)

(* TODO: project state *)
let get_context =
  let context = ref None in
  fun () ->
    match !context with
    | Some c -> c
    | None ->
      if Eva.Analysis.is_computed () then
        let c = Context.create () in
        context := Some c;
        c
      else
        begin
          Self.error ~once:true
            "A prior Eva analysis is required to build the graphs.";
          Server.Data.failure "Eva analysis not computed"
        end


let global_window = ref {
    perception = { backward = Some 2 ; forward = Some 1 };
    horizon = { backward = None ; forward = None };
  }


(* -------------------------------------------------------------------------- *)
(* --- Data types                                                         --- *)
(* -------------------------------------------------------------------------- *)

module Range : Data.S with type t = int option range =
struct
  type t = int option range
  let name = "range"
  let descr = Markdown.plain "Parametrization of the exploration range."
  let sign : t Record.signature = Record.signature ()

  module Fields =
  struct
    let backward = Record.field sign
        ~name:"backward"
        ~descr:(Markdown.plain "range for the write dependencies")
        (module Joption (Jint))

    let forward = Record.field sign
        ~name:"forward"
        ~descr:(Markdown.plain "range for the read dependencies")
        (module Joption (Jint))
  end

  module Record = (val Record.publish ~package ~name ~descr sign)

  let jtype = Record.jtype

  let to_json r =
    Record.default |>
    Record.set Fields.backward r.backward |>
    Record.set Fields.forward r.forward |>
    Record.to_json

  let of_json js =
    let r = Record.of_json js in
    {
      backward = Record.get Fields.backward r;
      forward = Record.get Fields.forward r;
    }
end


module Window : Data.S with type t = window =
struct
  type t = window
  let name = "explorationWindow"
  let descr = Markdown.plain "Global parametrization of the exploration."
  let sign : t Record.signature = Record.signature ()

  module Fields =
  struct
    let perception = Record.field sign
        ~name:"perception"
        ~descr:(Markdown.plain "how far dive will explore from root nodes ; \
                                must be a finite range")
        (module Range)

    let horizon = Record.field sign
        ~name:"horizon"
        ~descr:(Markdown.plain "range beyond which the nodes must be hidden")
        (module Range)
  end

  module Record = (val Record.publish ~package ~name ~descr sign)

  let jtype = Record.jtype

  let to_json w =
    Record.default |>
    Record.set Fields.perception w.perception |>
    Record.set Fields.horizon w.horizon |>
    Record.to_json

  let of_json js =
    let r = Record.of_json js in
    {
      perception = Record.get Fields.perception r;
      horizon = Record.get Fields.horizon r;
    }
end


module NodeId =
struct
  type t = node
  let name = "nodeId"
  let descr = Markdown.plain "A node identifier in the graph"

  let jtype = Data.declare ~package ~name ~descr Data.Jint.jtype

  let _to_json node =
    `Int node.node_key

  let of_json json =
    let node_key = Data.Jint.of_json json in
    try
      Context.find_node (get_context ()) node_key
    with Not_found ->
      Data.failure "no node '%d' in the current graph" node_key
end

module Callsite =
struct
  let name = "callsite"
  let descr = Markdown.plain "A callsite"
  let jtype = Data.declare ~package ~name ~descr (Jrecord [
      "fun", Jstring;
      "instr", Junion [ Jnumber ; Jstring ];
    ])
end

module Callstack =
struct
  let name = "callstack"
  let descr = Markdown.plain "The callstack context for a node"
  let jtype = Data.declare ~package ~name ~descr (Jarray Callsite.jtype)
end

module NodeLocality =
struct
  let name = "nodeLocality"
  let descr = Markdown.plain "The description of a node locality"
  let jtype = Data.declare ~package ~name ~descr (Jrecord [
      "file", Jstring;
      "callstack", Joption (Callstack.jtype)
    ])
end

module Node =
struct
  let name = "node"
  let descr = Markdown.plain "A graph node"
  let jtype = Data.declare ~package ~name ~descr (Jrecord [
      "id", NodeId.jtype;
      "label", Jstring;
      "kind", Jstring;
      "locality", NodeLocality.jtype;
      "is_root", Jboolean;
      "backward_explored", Jstring;
      "forward_explored", Jstring;
      "writes", Jarray Kernel_ast.KfMarker.jtype;
      "values", Joption Jstring;
      "range", Junion [ Jnumber ; Jstring ];
      "type", Joption Jstring
    ])
end

module Dependency =
struct
  let name = "dependency"
  let descr = Markdown.plain "The dependency between two nodes"
  let jtype = Data.declare ~package ~name ~descr (Jrecord [
      "id", Jnumber ;
      "src", NodeId.jtype ;
      "dst", NodeId.jtype ;
      "kind", Jstring ;
      "origins", Jarray Kernel_ast.KfMarker.jtype
    ])
end

module Graph =
struct
  type t = Dive_graph.t
  let name = "graphData"
  let descr = Markdown.plain "The whole graph being built"
  let jtype = Data.declare ~package ~name ~descr (Jrecord [
      "nodes", Jarray Node.jtype;
      "deps", Jarray Dependency.jtype
    ])

  let to_json = Dive_graph.to_json
end


module GraphDiff =
struct
  type t = Dive_graph.t * graph_diff
  let name = "diffData"
  let descr = Markdown.plain "Graph differences from the last action."
  let jtype = Data.declare ~package ~name ~descr (Jrecord [
      "root", Joption NodeId.jtype;
      "add", Jrecord [
        "nodes", Jarray Node.jtype;
        "deps", Jarray Dependency.jtype
      ];
      "sub", Jarray NodeId.jtype
    ])

  let to_json = fun (g,d) -> Dive_graph.diff_to_json g d
end


(* -------------------------------------------------------------------------- *)
(* --- Actions                                                            --- *)
(* -------------------------------------------------------------------------- *)

let result context last_root =
  let diff = Context.take_last_diff context in
  Context.get_graph context, { diff with last_root }

let finalize' context node_opt =
  begin match node_opt with
    | None -> ()
    | Some node ->
      let may_explore f =
        Option.iter (fun depth -> f ~depth context node)
      in
      may_explore Build.explore_backward !global_window.perception.backward;
      may_explore Build.explore_forward !global_window.perception.forward;
      let horizon = !global_window.horizon in
      if Option.is_some horizon.forward ||
         Option.is_some horizon.backward
      then
        Build.reduce_to_horizon context horizon node
  end;
  result context node_opt

let finalize context node =
  finalize' context (Some node)

let () = Request.register ~package
    ~kind:`SET ~name:"window"
    ~descr:(Markdown.plain "Set the exploration window")
    ~input:(module Window) ~output:(module Data.Junit)
    (fun window -> global_window := window)

let () = Request.register ~package
    ~kind:`GET ~name:"graph"
    ~descr:(Markdown.plain "Retrieve the whole graph")
    ~input:(module Data.Junit) ~output:(module Graph)
    (fun () -> Context.get_graph (get_context ()))

let () = Request.register ~package
    ~kind:`EXEC ~name:"clear"
    ~descr:(Markdown.plain "Erase the graph and start over with an empty one")
    ~input:(module Data.Junit) ~output:(module Data.Junit)
    (fun () -> Context.clear (get_context ()))

let () = Request.register ~package
    ~kind:`EXEC ~name:"add"
    ~descr:(Markdown.plain "Add a node to the graph")
    ~input:(module Kernel_ast.Marker) ~output:(module GraphDiff)
    begin fun loc ->
      let context = get_context () in
      finalize' context (Build.add_localizable context loc)
    end

let () = Request.register ~package
    ~kind:`EXEC ~name:"explore"
    ~descr:(Markdown.plain "Explore the graph starting from an existing vertex")
    ~input:(module NodeId) ~output:(module GraphDiff)
    begin fun node ->
      let context = get_context () in
      Build.show context node;
      finalize context node
    end

let () = Request.register ~package
    ~kind:`EXEC ~name:"show"
    ~descr:(Markdown.plain "Show the dependencies of an existing vertex")
    ~input:(module NodeId) ~output:(module GraphDiff)
    begin fun node ->
      let context = get_context () in
      Build.show context node;
      Build.explore_backward ~depth:1 context node;
      finalize' context None
    end

let () = Request.register ~package
    ~kind:`EXEC ~name:"hide"
    ~descr:(Markdown.plain "Hide the dependencies of an existing vertex")
    ~input:(module NodeId) ~output:(module GraphDiff)
    begin fun node ->
      let context = get_context () in
      Build.hide context node;
      finalize' context None
    end
