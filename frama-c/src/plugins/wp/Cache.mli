(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

type mode = NoCache | Update | Replay | Rebuild | Offline | Cleanup

val get_dir : unit -> string

val set_mode : mode -> unit
val get_mode : unit -> mode
val get_hits : unit -> int
val get_miss : unit -> int
val get_removed : unit -> int

val is_updating : unit -> bool

val cleanup_cache : unit -> unit

type 'a digest = Why3Provers.t -> 'a -> string

type 'a runner =
  timeout:int option -> steplimit:int option -> Why3Provers.t -> 'a ->
  VCS.result Task.task

val get_result: digest:('a digest) -> runner:('a runner) -> 'a runner
val clear_result: digest:('a digest) -> Why3Provers.t -> 'a -> unit

(**************************************************************************)
