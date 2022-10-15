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

(* ************************************************************************** *)
(** {2 Generic code} *)
(* ************************************************************************** *)

let warn_rte warn exn =
  if warn then
    Options.warning "@[@[cannot run RTE:@ %s.@]@ \
                     Ignoring potential runtime errors in annotations."
      (Printexc.to_string exn)

(* ************************************************************************** *)
(** {2 Exported code} *)
(* ************************************************************************** *)

open Cil_datatype

let stmt ?(warn=true) =
  try
    Dynamic.get
      ~plugin:"RteGen"
      "stmt_annotations"
      (Datatype.func2 Kernel_function.ty Stmt.ty
         (let module L = Datatype.List(Code_annotation) in L.ty))
  with Failure _ | Dynamic.Unbound_value _ | Dynamic.Incompatible_type _ as exn
    ->
    warn_rte warn exn;
    fun _ _ -> []

let exp ?(warn=true) =
  try
    Dynamic.get
      ~plugin:"RteGen"
      "exp_annotations"
      (Datatype.func3 Kernel_function.ty Stmt.ty Exp.ty
         (let module L = Datatype.List(Code_annotation) in L.ty))
  with Failure _ | Dynamic.Unbound_value _ | Dynamic.Incompatible_type _ as exn
    ->
    warn_rte warn exn;
    fun _ _ _ -> []

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
