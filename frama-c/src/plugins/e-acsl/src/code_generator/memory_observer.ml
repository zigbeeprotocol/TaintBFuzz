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

open Cil_datatype

let tracking_stmt fold mk_stmt env kf vars =
  if Functions.instrument kf then
    fold
      (fun vi env ->
         if Memory_tracking.must_monitor_vi ~kf vi then
           Env.add_stmt env (mk_stmt vi)
         else
           env)
      vars
      env
  else
    env

let store env kf vars =
  tracking_stmt
    List.fold_right (* small list *)
    Smart_stmt.store_stmt
    env
    kf
    vars

let duplicate_store env kf vars =
  tracking_stmt
    Varinfo.Set.fold
    Smart_stmt.duplicate_store_stmt
    env
    kf
    vars

let delete_from_list env kf vars =
  tracking_stmt
    List.fold_right (* small list *)
    Smart_stmt.delete_stmt
    env
    kf
    vars

let delete_from_set env kf vars =
  tracking_stmt
    Varinfo.Set.fold
    Smart_stmt.delete_stmt
    env
    kf
    vars

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
