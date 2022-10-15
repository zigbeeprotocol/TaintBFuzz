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

include Plugin.S

module type Varinfo_set = Parameter_sig.Set
  with type elt = Cil_types.varinfo
   and type t = Cil_datatype.Varinfo.Set.t

module OutputDot : Parameter_sig.Filepath
module OutputJson : Parameter_sig.Filepath
module DepthLimit : Parameter_sig.Int
module FromFunctionAlarms : Parameter_sig.Kernel_function_set
module FromBases : Varinfo_set
module UnfoldedBases : Varinfo_set
module HiddenBases : Varinfo_set
