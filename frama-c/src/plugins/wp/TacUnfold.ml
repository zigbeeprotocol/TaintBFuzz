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

open Lang
open Tactical
open Conditions

(* -------------------------------------------------------------------------- *)
(* --- Unfold Definition Tactical                                         --- *)
(* -------------------------------------------------------------------------- *)

open Definitions

let definition f es =
  let d = find_symbol f in
  match d.d_definition with
  | Function(_,_,u) ->
    let sigma = Lang.subst d.d_params es in
    F.e_subst sigma u
  | Predicate(_,p) ->
    let sigma = Lang.subst d.d_params es in
    F.e_prop (F.p_subst sigma p)
  | _ ->
    raise Not_found

let range f es =
  let a,b = Ctypes.bounds (Cint.is_cint f) in
  let range e = F.p_and
      (F.p_leq (F.e_zint a) e)
      (F.p_leq e (F.e_zint b)) in
  F.e_prop (F.p_all range es)

(* Used only for non Multi selection *)

let rec applicable ?at e f es = function
  | phi::others ->
    begin
      try
        let v = phi f es in
        let d = Format.asprintf "Unfold '%a'" Lang.Fun.pretty f in
        Applicable (Tactical.rewrite ?at [d,F.p_true,e,v])
      with Not_found | Invalid_argument _ ->
        applicable ?at e f es others
    end
  | [] ->
    Not_applicable

(* Used only for Multi selection *)

module Smap = Qed.Idxmap.Make
    (struct
      type t = step
      let id s = s.id
    end)

let condition original p = (* keep original kind of simple condition *)
  match original.condition with
  | Type _ -> Type p
  | Have _ -> Have p
  | When _ -> When p
  | Core _ -> Core p
  | Init _ -> Init p
  | _ -> assert false

let collect_term_to_unfold (g, m) = function
  | Inside(Step step, unfold) ->
    let l =
      try Smap.find step m
      with Not_found -> []
    in
    g, Smap.add step (unfold :: l) m
  | Inside (Goal _, unfold) ->
    begin match g with
      | None -> Some [ unfold ], m
      | Some g -> Some (unfold :: g), m
    end
  | _ -> raise Not_found

let rec collect_unfold phis m e =
  match phis with
  | phi :: others ->
    begin
      try
        match F.repr e with
        | Qed.Logic.Fun(f,es) -> Lang.F.Tmap.add e (phi f es) m
        | _ -> raise Not_found
      with Not_found | Invalid_argument _ -> collect_unfold others m e
    end
  | [] -> m

let unfolds_from_list phis es =
  List.fold_left (collect_unfold phis) Lang.F.Tmap.empty es

let unfolds_from_smap phis m =
  Smap.map (fun _s es -> unfolds_from_list phis es) m

module Unfoldedset = Qed.Listset.Make(Lang.Fun)

let tactical_inside step unfolds sequent =
  if Lang.F.Tmap.is_empty unfolds
  then raise Not_found
  else match step.condition with
    | Type p | Have p | When p | Core p | Init p ->
      let unfolded = ref Unfoldedset.empty in
      let subst t =
        let result = Lang.F.Tmap.find t unfolds in
        begin match F.repr t with
          | Qed.Logic.Fun(f,_) -> unfolded := Unfoldedset.add f !unfolded
          | _ -> ()
        end ;
        result
      in
      let p = condition step @@ Lang.p_subst subst p in
      let feedback =
        let pp fmt f = Format.fprintf fmt "'%a'" Lang.Fun.pretty f in
        Format.asprintf "Unfold %a"
          (Pretty_utils.pp_list ~sep:", " pp) !unfolded
      in
      !unfolded, snd @@ Tactical.replace_single ~at:step.id (feedback, p) sequent
    | _ -> raise Not_found

let tactical_goal unfolds (seq, g) =
  if Lang.F.Tmap.is_empty unfolds
  then raise Not_found
  else
    let subst t = Lang.F.Tmap.find t unfolds in
    seq, Lang.p_subst subst g

let fold_selection goal_unfolds step_unfolds sequent =
  let tactical s l (acc_unfolded, seq) =
    let unfolded, seq = tactical_inside s l seq in
    Unfoldedset.union unfolded acc_unfolded, seq
  in
  let unfolded, seq = Smap.fold tactical step_unfolds ([], sequent) in
  let feedback =
    let pp fmt f = Format.fprintf fmt "'%a'" Lang.Fun.pretty f in
    Format.asprintf "Unfold %a"
      (Pretty_utils.pp_list ~sep:", " pp) unfolded
  in
  let add_goal = match goal_unfolds with
    | None -> Extlib.id
    | Some goal_unfolds -> tactical_goal goal_unfolds
  in
  feedback, add_goal seq

let process (f: sequent -> string * sequent) s = [ f s ]

class unfold =
  object
    inherit Tactical.make ~id:"Wp.unfold"
        ~title:"Definition"
        ~descr:"Unfold predicate and logic function definition"
        ~params:[]

    method select _feedback (s : Tactical.selection) =
      let unfoldings = [ definition ; range ] in
      match s with
      | Multi es ->
        let goal, steps =
          List.fold_left collect_term_to_unfold (None, Smap.empty) es in
        let goal = Option.map (unfolds_from_list unfoldings) goal in
        let steps = unfolds_from_smap unfoldings steps in
        Applicable (process @@ fold_selection goal steps)
      | s ->
        let at = Tactical.at s in
        let e = Tactical.selected s in
        match F.repr e with
        | Qed.Logic.Fun(f,es) ->
          applicable ?at e f es unfoldings
        | _ -> Not_applicable
  end

let tactical = Tactical.export (new unfold)
let strategy = Strategy.make tactical ~arguments:[]
