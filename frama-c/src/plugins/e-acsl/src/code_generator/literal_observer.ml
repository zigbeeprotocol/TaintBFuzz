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

let literal loc env kf s =
  try
    let vi = Literal_strings.find s in
    (* if the literal string was already created, just get it. *)
    Cil.evar ~loc vi, env
  with Not_found ->
    (* never seen this string before: replace it by a new global var *)
    let vi, exp, env =
      Env.new_var
        ~loc
        ~scope:Varname.Global
        ~name:"literal_string"
        env
        kf
        None
        Cil.charPtrType
        (fun _ _ -> [] (* done in the initializer, see {!vglob_aux} *))
    in
    Literal_strings.add s vi;
    exp, env

let subst_all_literals_in_exp env kf e =
  let env_ref = ref env in
  let o = object
    inherit Cil.genericCilVisitor (Visitor_behavior.copy (Project.current ()))
    method !vlval _ = Cil.SkipChildren (* no literal string in left values *)
    method !vexpr e = match e.enode with
      (* the guard below could be optimized: if no annotation depends on this
         string, then it is not required to monitor it.
         (currently, the guard says: "no annotation uses the memory model" *)
      | Const (CStr s) when Memory_tracking.use_monitoring () ->
        let e, env = literal e.eloc !env_ref kf s in
        env_ref := env;
        Cil.ChangeTo e
      | _ ->
        Cil.DoChildren
  end in
  let e = Cil.visitCilExpr o e in
  e, !env_ref

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
