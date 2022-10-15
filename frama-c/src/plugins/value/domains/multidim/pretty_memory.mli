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

type 'a sformat = ('a,Format.formatter,unit) format
type 'a formatter = Format.formatter -> 'a -> unit

(* Pretty printing for iterators *)

val pp_iter :
  ?pre:unit sformat ->
  ?sep:unit sformat ->
  ?suf:unit sformat ->
  ?format:('a formatter -> 'a -> unit) sformat ->
  (('a -> unit) -> 'b -> unit) ->
  'a formatter -> 'b formatter

val pp_iter2 :
  ?pre:(unit sformat) ->
  ?sep:(unit sformat) ->
  ?suf:(unit sformat) ->
  ?format:('a formatter -> 'a -> 'b formatter -> 'b -> unit) sformat ->
  (('a -> 'b -> unit) -> 'c -> unit) ->
  'a formatter -> 'b formatter -> 'c formatter
