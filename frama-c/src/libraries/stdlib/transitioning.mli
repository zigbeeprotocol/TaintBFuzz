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

(** This file contains functions available in recent OCaml releases but
    unavailable in the oldest OCaml version officially supported by Frama-C. Be
    sure to update it when support for a given version is dropped.

    Functions are grouped according to the module of the stdlib they
    emulate. The mentioned OCaml version indicate when the function was
    introduced in the stdlib (i.e. when Frama-C requires a version higher
    than that, it can safely be removed from Transitioning).
*)

(** {1 OCaml} *)

module List: sig
  (** since 4.10.0 *)
  val concat_map: ('a -> 'b list) -> 'a list -> 'b list

  (** since 4.12.0 *)
  val equal: ('a -> 'a -> bool) -> 'a list -> 'a list -> bool

  (** since 4.12.0 *)
  val compare: ('a -> 'a -> int) -> 'a list -> 'a list -> int
end
