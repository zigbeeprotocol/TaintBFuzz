(**************************************************************************)
(*                                                                        *)
(*  This file is part of the Frama-C's E-ACSL plug-in.                    *)
(*                                                                        *)
(*  Copyright (C) 2012-2021                                               *)
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

val comparison_to_exp: loc:location -> kernel_function -> Env.t ->
  name:string -> binop -> exp -> exp -> exp * Env.t
(** [comparison_to_exp ~loc kf env ~name bop e1 e2] generate the C code
    equivalent to [e1 bop e2].
    Requires that [bop] is either [Ne] or [Eq] and that [e1] and [e2] are
    arrays. *)


(**************************************************************************)
(********************** Forward references ********************************)
(**************************************************************************)

val translate_rte_ref:
  (?filter:(code_annotation -> bool) -> kernel_function -> Env.t -> exp ->
   Env.t) ref
