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

(* inspired by Pretty_utils.pp_iter *)

let pp_iter
    ?(pre=format_of_string "{@;<1 2>")
    ?(sep=format_of_string ",@;<1 2>")
    ?(suf=format_of_string "@ }")
    ?(format=format_of_string "@[<hv>%a@]")
    iter pp fmt v =
  let need_sep = ref false in
  Format.fprintf fmt pre;
  iter (fun v ->
      if !need_sep then Format.fprintf fmt sep else need_sep := true;
      Format.fprintf fmt format pp v;
    ) v;
  Format.fprintf fmt suf

let pp_iter2 ?pre ?sep ?suf ?(format=format_of_string "@[<hv>%a%a@]")
    iter2 pp_key pp_val fmt v =
  let iter f = iter2 (fun k v -> f (k,v)) in
  let pp fmt (k,v) = Format.fprintf fmt format pp_key k pp_val v in
  pp_iter ?pre ?sep ?suf ~format:"%a" iter pp fmt v
