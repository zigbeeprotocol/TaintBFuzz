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

(** Generate and translate RTE annotations. *)

open Cil_types
let dkey = Options.Dkey.translation

let rte_annots pp elt kf env l =
  let old_kind = Env.annotation_kind env in
  let env = Env.set_annotation_kind env RTE in
  let env =
    List.fold_left
      (fun env a -> match a.annot_content with
         | AAssert(_, p) ->
           Env.handle_error
             (fun env ->
                Options.feedback ~dkey ~level:4 "prevent RTE from %a" pp elt;
                (* The logic scope MUST NOT be reset here since we still might
                   be in the middle of the translation of the original
                   predicate. *)
                let lscope_reset_old = Env.Logic_scope.get_reset env in
                let env = Env.Logic_scope.set_reset env false in
                let env =
                  Env.with_params
                    ~rte:false
                    ~f:(fun env -> Translate_predicates.do_it kf env p)
                    env
                in
                let env = Env.Logic_scope.set_reset env lscope_reset_old in
                env)
             env
         | _ -> assert false)
      env
      l
  in
  Env.set_annotation_kind env old_kind

let () =
  Translate_predicates.translate_rte_annots_ref := rte_annots

let exp ?filter kf env e =
  let stmt = Cil.mkStmtOneInstr ~valid_sid:true (Skip e.eloc) in
  let l = Rte.exp kf stmt e in
  let l =
    match filter with
    | Some f -> List.filter f l
    | None -> l
  in
  List.iter (Typing.preprocess_rte ~lenv:(Env.Local_vars.get env)) l;
  rte_annots Printer.pp_exp e kf env l

let () =
  Translate_terms.translate_rte_exp_ref := exp;
  Translate_predicates.translate_rte_exp_ref := exp;
  Logic_array.translate_rte_ref := exp

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
