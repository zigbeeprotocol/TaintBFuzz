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

open LogicUsage

(* -------------------------------------------------------------------------- *)
(* --- VC Generator                                                       --- *)
(* -------------------------------------------------------------------------- *)

module type VCgen =
sig
  include Mcfg.S
  val register_lemma : logic_lemma -> unit
  val compile_lemma : logic_lemma -> Wpo.t
  val compile_wp : Wpo.index -> t_prop -> Wpo.t Bag.t
end

val vcgen : Factory.setup -> Factory.driver -> (module VCgen)

(* -------------------------------------------------------------------------- *)
