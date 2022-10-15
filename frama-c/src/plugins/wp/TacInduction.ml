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

(* remove parts with n from p into hs accumulator *)
let filter_pred n hs p  =
  F.p_conj @@ List.filter
    (fun p -> if F.occursp n p then (hs := p :: !hs ; false) else true)
    (match F.p_expr p with And ps -> ps | _ -> [p])

(* remove parts with n from step s into hs accumulator *)
let filter_step n hs s =
  match s.Conditions.condition with
  | (Have _ | Type _ | Core _ | Init _ | When _)  ->
    Conditions.map_step (filter_pred n hs) s
  | (State _ | Branch _ | Either _) as c ->
    if F.Vars.mem n s.vars then
      (hs := Conditions.pred_cond c :: !hs ; Conditions.step (Have F.p_true))
    else s

let filter_seq n hs seq =
  Conditions.sequence @@ List.map (filter_step n hs) @@ Conditions.list seq

let process value n0 sequent =

  (* Transfrom seq into: hyps => (forall n, goal) *)
  let n = Lang.freshvar ~basename:"n" Qed.Logic.Int in
  let i = Lang.freshvar ~basename:"i" Qed.Logic.Int in
  let vn = F.e_var n in
  let vi = F.e_var i in
  let sigma = Lang.sigma () in
  F.Subst.add sigma value vn ;
  let seq, goal = Conditions.map_sequent (F.p_subst sigma) sequent in
  let hind = ref [] in
  let seq = filter_seq n hind seq in
  let goal_n = F.p_hyps !hind goal in
  let goal_i = F.p_subst_var n vi goal_n in

  (* Base: n = n0 *)
  let goal_base = F.p_imply (F.p_equal vn n0) goal_n in

  (* Hind: n0 <= i < n *)
  let goal_sup =
    let hsup = [ F.p_leq n0 vi ; F.p_lt vi vn ] in
    let hind = F.p_forall [i] (F.p_hyps hsup goal_i) in
    F.p_hyps [F.p_lt n0 vn; hind] goal_n in

  (* Hind: n < i <= n0 *)
  let goal_inf =
    let hinf = [ F.p_lt vn vi ; F.p_leq vi n0 ] in
    let hind = F.p_forall [i] (F.p_hyps hinf goal_i) in
    F.p_hyps [F.p_lt vn n0; hind] goal_n in

  (* All Cases *)
  List.map (fun (name,goal) -> name , (seq,goal)) [
    "Base" , goal_base ;
    "Induction (sup)" , goal_sup ;
    "Induction (inf)" , goal_inf ;
  ]

(* -------------------------------------------------------------------------- *)
(* --- Induction Tactical                                                 --- *)
(* -------------------------------------------------------------------------- *)

let vbase,pbase = Tactical.composer ~id:"base"
    ~title:"Base" ~descr:"Value of base case" ()

class induction =
  object(self)
    inherit Tactical.make
        ~id:"Wp.induction"
        ~title:"Induction"
        ~descr:"Proof by integer induction"
        ~params:[pbase]

    method private get_base () =
      match self#get_field vbase with
      | Tactical.Compose(Code(t, _, _))
      | Inside(_, t) when Lang.F.typeof t = Lang.t_int ->
        Some t
      | Compose(Cint i) ->
        Some (Lang.F.e_bigint i)
      | _ ->
        None

    method select feedback (s : Tactical.selection) =
      begin match self#get_field vbase with
        | Empty ->
          self#set_field vbase (Tactical.int 0) ;
          feedback#update_field vbase
        | _ -> ()
      end ;
      let value = Tactical.selected s in
      if F.is_int value then
        match self#get_base () with
        | Some base -> Tactical.Applicable(process value base)
        | None -> Not_configured
      else Not_applicable

  end

let tactical = Tactical.export (new induction)

(* -------------------------------------------------------------------------- *)
