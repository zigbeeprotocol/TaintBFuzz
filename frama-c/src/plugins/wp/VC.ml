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

open Wpo

(* -------------------------------------------------------------------------- *)
(* --- Verification Conditions Interface                                  --- *)
(* -------------------------------------------------------------------------- *)

type t = Wpo.t

let get_id = Wpo.get_gid
let get_model = Wpo.get_model
let get_scope = Wpo.get_scope
let get_context = Wpo.get_context
let get_description = Wpo.get_label
let get_property = Wpo.get_property
let get_sequent w = snd (Wpo.compute w)
let get_result = Wpo.get_result
let get_results = Wpo.get_results
let get_logout = Wpo.get_file_logout
let get_logerr = Wpo.get_file_logerr
let is_trivial = Wpo.is_trivial
let is_proved = Wpo.is_proved

let get_formula po =
  match po.po_formula with
  | GoalLemma l -> l.VC_Lemma.lemma.Definitions.l_lemma
  | GoalAnnot { VC_Annot.goal = g } ->
    WpContext.on_context
      (get_context po) (Wpo.GOAL.compute_proof ~pid:po.po_pid) g

let clear = Wpo.clear
let proof = Wpo.goals_of_property
let iter_ip on_goal ip = Wpo.iter ~ip ~on_goal ()
let iter_kf on_goal ?bhv kf =
  match bhv with
  | None ->
    (* iter on all behaviors, see Wpo.iter *)
    Wpo.iter ~index:(Wpo.Function(kf,None)) ~on_goal ()
  | Some bs ->
    List.iter
      (fun b ->
         Wpo.iter ~index:(Wpo.Function(kf,Some b)) ~on_goal ()
      ) bs

let remove = iter_ip Wpo.remove
let () = Property_status.register_property_remove_hook remove

(* -------------------------------------------------------------------------- *)
(* --- Generator Interface                                                --- *)
(* -------------------------------------------------------------------------- *)

let generator model =
  let setup = match model with
    | None -> None
    | Some s -> Some (Factory.parse [s]) in
  Generator.create ~dump:false ?setup ()

let generate_ip ?model ip =
  (generator model)#compute_ip ip

let generate_kf ?model ?bhv ?prop kf =
  let kfs = Kernel_function.Set.singleton kf in
  (generator model)#compute_main ~fct:(Fct_list kfs) ?bhv ?prop ()

let generate_call ?model stmt =
  (generator model)#compute_call stmt

(* -------------------------------------------------------------------------- *)
(* --- Prover Interface                                                   --- *)
(* -------------------------------------------------------------------------- *)

let prove = Prover.prove
let spawn = Prover.spawn ~delayed:true

let server = ProverTask.server
let command ?provers ?tip vcs =
  Register.do_wp_proofs ?provers ?tip vcs

(* -------------------------------------------------------------------------- *)
