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

(** [get_edges s1 s2 g] retrieves all edges in [g] between [s1] and [s2]. *)
val get_edges:
  Promelaast.state -> Promelaast.state -> ('c,'a) Promelaast.graph
  -> ('c, 'a) Promelaast.trans list

(** retrieve all edges starting at the given node. *)
val get_transitions_of_state:
  Promelaast.state -> ('c,'a) Promelaast.graph -> ('c,'a) Promelaast.trans list

(** return the initial states of the graph. *)
val get_init_states: ('c, 'a) Promelaast.graph -> Promelaast.state list

(** [true] iff there's at most one path between the two states in the graph. *)
val at_most_one_path:
  ('c, 'a) Promelaast.graph -> Promelaast.state -> Promelaast.state -> bool
