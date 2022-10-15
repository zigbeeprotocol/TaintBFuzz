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

(** An interpreted automaton is a convenient formalization of programs for
    abstract interpretation. It is a control flow graph where states are
    control point and edges are transitions. It keeps track of conditions
    on which a transition can be taken (guards) as well as actions which are
    computed when a transition is taken. It can then be interpreted w.r.t. the
    operational semantics to reproduce the behavior of the program or
    w.r.t. to the collection semantics to compute a set of reachable states.

    This intermediate representation abstracts almost completely the notion of
    statement in CIL. Edges are either CIL expressions for guards, CIL
    instructions for actions or a return Edge. Thus, it saves the higher
    abstraction layers from interpreting CIL statements and from attaching
    guards to statement successors. *)

type info =
  | NoneInfo
  | LoopHead of int (* level *)

(** Control flow informations for outgoing edges, if any. *)
type 'a control =
  | Edges (** control flow is only given by vertex edges. *)
  | Loop of 'a (** start of a Loop stmt, with breaking vertex. *)
  | If of { cond: exp; vthen: 'a; velse: 'a }
  (** edges are guaranteed to be two guards `Then` else `Else`
      with the given condition and successor vertices. *)
  | Switch of { value: exp; cases: (exp * 'a) list; default: 'a }
  (** edges are guaranteed to be issued from a `switch()` statement with
      the given cases and default vertices. *)

(** Vertices are control points. When a vertice is the *start* of a statement,
    this statement is kept in vertex_stmt. Currently, this statement is kept for
    two reasons: to know when callbacks should be called and when annotations
    should be read. *)

type vertex = private {
  vertex_key : int;
  mutable vertex_start_of : Cil_types.stmt option;
  mutable vertex_info : info;
  mutable vertex_control : vertex control;
}

type assert_kind =
  | Invariant
  | Assert
  | Check
  | Assume

(** Maps binding the labels from an annotation to the vertices they refer to in
    the graph. *)
type 'vertex labels = 'vertex Cil_datatype.Logic_label.Map.t

type 'vertex annotation = {
  kind: assert_kind;
  predicate: identified_predicate;
  labels: 'vertex labels;
  property: Property.t;
}

(** Each transition can either be a skip (do nothing), a return, a guard
    represented by a Cil expression, a Cil instruction, an ACSL annotation
    or entering/leaving a block.
    The edge is annotated with the statement from which the transition has been
    generated. This is currently used to choose alarms locations. *)
type 'vertex transition =
  | Skip
  | Return of exp option * stmt
  | Guard of exp * guard_kind * stmt
  | Prop of 'vertex annotation * stmt
  | Instr of instr * stmt
  | Enter of block
  | Leave of block

and guard_kind = Then | Else

val pretty_transition: vertex transition Pretty_utils.formatter

type 'vertex edge = private {
  edge_key : int;
  edge_kinstr : kinstr;
  edge_transition : 'vertex transition;
  edge_loc : location;
}

val pretty_edge: vertex edge Pretty_utils.formatter

module G : Graph.Sig.I
  with type V.t = vertex
   and  type E.t = vertex * vertex edge * vertex
   and  type V.label = vertex
   and  type E.label = vertex edge

type graph = G.t

(** Weak Topological Order is given by a list (in topological order) of
    components of the graph, which are themselves WTOs *)
type wto = vertex Wto.partition

(** Datatype for vertices *)
module Vertex : Datatype.S_with_collections with type t = vertex

(** Datatype for edges *)
module Edge : Datatype.S_with_collections with type t = vertex edge



(** An interpreted automaton for a given function is a graph whose edges are
    guards and commands and always containing two special nodes which are the
    entry point and the return point of the function. It also comes with
    a table linking Cil statements to their starting and ending vertex *)

type automaton = {
  graph : graph;
  entry_point : vertex;
  return_point : vertex;
  stmt_table : (vertex * vertex) Cil_datatype.Stmt.Hashtbl.t;
}

(** Datatype for automata *)
module Automaton : Datatype.S with type t = automaton

(** Datatype for WTOs *)
module WTO : sig
  include module type of (Wto.Make(Vertex))
  include Datatype.S with type t = wto
end

(** Get the automaton for the given kernel_function without annotations *)
val get_automaton : Cil_types.kernel_function -> automaton

(** Get the wto for the automaton of the given kernel_function *)
val get_wto : Cil_types.kernel_function -> wto

(** Extract an exit strategy from a component, i.e. a sub-wto where all
    vertices lead outside the wto without passing through the head. *)
val exit_strategy : graph -> vertex Wto.component -> wto

type 'a labeling =
  [ `Stmt
  | `Vertex
  | `Both
  | `Custom of Format.formatter -> 'a -> unit
  ]

(** Output the automaton in dot format *)
val output_to_dot : out_channel -> ?labeling:vertex labeling -> ?wto:wto ->
  automaton -> unit

(** the position of a statement in a wto given as the list of
    component heads *)
type wto_index = vertex list

(** Datatype for wto_index *)
module WTOIndex : Datatype.S with type t = wto_index

(** @return the wto_index for a statement *)
val get_wto_index :
  Cil_types.kernel_function -> vertex -> wto_index

(** @return the components left and the components entered when going from
    one index to another *)
val wto_index_diff :
  wto_index -> wto_index -> vertex list * vertex list

(** @return the components left and the components entered when going from
    one vertex to another *)
val get_wto_index_diff :
  Cil_types.kernel_function -> vertex -> vertex -> vertex list * vertex list

(** @return wether [v] is a component head or not *)
val is_wto_head :
  Cil_types.kernel_function -> vertex -> bool

(** @return wether [v1,v2] is a back edge of a loop, i.e. if the vertex v1
    is a wto head of any component where v2 is included. This assumes that
    (v1,v2) is actually an edge present in the control flow graph. *)
val is_back_edge :
  Cil_types.kernel_function -> vertex * vertex -> bool

(** This module defines the previous functions without memoization *)
module Compute: sig

  (** Get the interpreted automaton for the given kernel_function.
      Note that the automata construction may lead to the build of new Cil
      expressions which will be different at each call: you may need to
      memoize the results of this function. *)
  val get_automaton : annotations:bool -> Cil_types.kernel_function -> automaton

  (** Build the wto for the given automaton (No memoization, use get_wto
      instead) *)
  val build_wto : automaton -> wto

  (** Extract an exit strategy from a component, i.e. a sub-wto where all
      vertices lead outside the wto without passing through the head. *)
  val exit_strategy : graph -> vertex Wto.component -> wto

  (** Output the automaton in dot format *)
  val output_to_dot : out_channel -> ?labeling:vertex labeling  -> ?wto:wto ->
    automaton -> unit


  type wto_index_table

  (** Compute the index table from a wto *)
  val build_wto_index_table: wto -> wto_index_table

  (** @return the wto_index for a statement *)
  val get_wto_index :
    wto_index_table -> vertex -> wto_index

  (** @return the components left and the components entered when going from
      one index to another *)
  val wto_index_diff :
    wto_index -> wto_index -> vertex list * vertex list

  (** @return the components left and the components entered when going from
      one vertex to another *)
  val get_wto_index_diff :
    wto_index_table -> vertex -> vertex -> vertex list * vertex list

  (** @return wether [v] is a component head or not *)
  val is_wto_head :
    wto_index_table -> vertex -> bool

  (** @return wether [v1,v2] is a back edge of a loop, i.e. if the vertex v1
      is a wto head of any component where v2 is included. This assumes that
      (v1,v2) is actually an edge present in the control flow graph. *)
  val is_back_edge :
    wto_index_table -> vertex * vertex -> bool

end

module UnrollUnnatural : sig
  (** Could enter a loop only by head nodes *)

  module Vertex_Set:
    Datatype.S_with_collections with type t = Vertex.Set.t
  module Version:
    Datatype.S_with_collections with type t = Vertex.t * Vertex.Set.t

  module G : sig
    include Graph.Sig.I
      with type V.t = Version.t
       and  type E.t = Version.t * Version.t edge * Version.t
       and  type V.label = Version.t
       and  type E.label = Version.t edge
    val pretty : t Pretty_utils.formatter
  end


  module WTO : sig
    include module type of (Wto.Make(Version))
    include Datatype.S with type t = Version.t Wto.partition
  end

  val output_to_dot : out_channel -> ?labeling:Version.t labeling ->
    ?wto:WTO.t -> G.t -> unit

  val unroll_unnatural_loop :
    automaton -> wto -> Compute.wto_index_table -> G.t

end


(** Dataflow computation: simple data-flow analysis using interpreted automata.
    See tests/misc/interpreted_automata_dataflow.ml for a complete example
    using this dataflow computation. *)

(** Input domain for a simple dataflow analysis. *)
module type Domain =
sig
  type t (** States propagated by the dataflow analysis. *)

  (** Merges two states coming from different paths. *)
  val join : t -> t -> t

  (** [widen v1 v2] must returns None if [v2] is included in [v1].
      Otherwise, over-approximates the join between [v1] and [v2] such that
      any sequence of successive widenings is ultimately stationary,
      i.e. […widen (widen (widen x0 x1) x2) x3…] eventually returns None.
      Called on loop heads to ensure the analysis termination. *)
  val widen : t -> t -> t option

  (** Transfer function for transitions: computes the state after the transition
      from the state before. Returns None if the end of the transition is not
      reachable from the given state. *)
  val transfer : vertex transition ->  t -> t option
end

(** Simple dataflow analysis *)
module type DataflowAnalysis =
sig
  type state
  type result

  val fixpoint : ?wto:wto -> Cil_types.kernel_function ->  state -> result

  module Result :
  sig
    (** Extract the result at the entry point of the analysed function *)
    val at_entry : result -> state option

    (** Extract the result at the return point of the analysed function (just
        after the return transfer function) *)
    val at_return : result -> state option

    (** Extract the result obtained for the control point immediately before the
        given statement *)
    val before : result -> Cil_types.stmt -> state option

    (** Extract the result obtained for the control point immediately after the
        given statement *)
    val after : result -> Cil_types.stmt -> state option

    (** Iter on the results obtained at each vertex of the graph.
        Do nothing  when the vertex is not reachable (for instance if transfer
        returned None) *)
    val iter_vertex : (vertex -> state -> unit) -> result -> unit

    (** Iter on the results obtained before each statements of the function.
        Do nothing  when the vertex is not reachable (for instance if transfer
        returned None) *)
    val iter_stmt : (Cil_types.stmt -> state -> unit) -> result -> unit

    (** Output result to the given channel. Must be supplied with a pretty
        printer for abstract values *)
    val to_dot_output : (Format.formatter -> state -> unit) ->
      result -> out_channel -> unit

    (** Output result to a file with the given path. Must be supplied with
        pretty printer for abstract values *)
    val to_dot_file : (Format.formatter -> state -> unit) ->
      result -> Filepath.Normalized.t -> unit

    (** Extract the result as a table from control points to states *)
    val as_table : result -> state Vertex.Hashtbl.t
  end
end

(** Forward dataflow analysis. The domain must provide a forward [transfer]
    function that computes the state after a transition from the state before. *)
module ForwardAnalysis (D : Domain) : DataflowAnalysis
  with type state = D.t

(** Backward dataflow analysis. The domain must provide a backward [transfer]
    function that computes the state before a transition from the state after. *)
module BackwardAnalysis (D : Domain) : DataflowAnalysis
  with type state = D.t
