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

module Typ : sig
  val params : typ -> (string * typ * attributes) list
  val ghost_partitioned_params : typ ->
    (string * typ * attributes) list *
    (string * typ * attributes) list
  val params_types : typ -> typ list
  val params_count : typ -> int
end

module List : sig
  include module type of List

  val make : int -> 'a -> 'a list
  val take : int -> 'a list -> 'a list
  val drop : int -> 'a list -> 'a list
  val break : int -> 'a list -> 'a list * 'a list
  val mapi2 : (int -> 'a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val ifind : ('a -> bool) -> 'a list -> int
end
