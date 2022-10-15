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

open Tactical
open Conditions

let condition original p = (* keep original kind of simple condition *)
  match original.condition with
  | Type _ -> Type p
  | Have _ -> Have p
  | When _ -> When p
  | Core _ -> Core p
  | Init _ -> Init p
  | _ -> assert false

let tactical_step step =
  Tactical.replace_single ~at:step.id
    (* Note: the provided name is used in the GUi for the subgoal title *)
    ("Removed Step", Conditions.Have Lang.F.p_true)

module Filtered =
struct
  type t =
    | Fun of Lang.Fun.t
    | Other of Lang.F.term

  let of_term t =
    match Lang.F.repr t with
    | Qed.Logic.Fun(f, _) -> Fun f
    | _ -> Other t

  let pretty fmt = function
    | Fun f -> Format.fprintf fmt "%a(...)" Lang.Fun.pretty f
    | Other t -> Lang.F.pp_term fmt t

  let compare a b =
    match a, b with
    | Fun a, Fun b -> Lang.Fun.compare a b
    | Other a, Other b -> Lang.F.compare a b
    | Fun _, _ -> 1
    | _, Fun _ -> -1

  let equal a b = 0 = compare a b
end

module TermLset = Qed.Listset.Make(Lang.F.QED.Term)
module Filteredset = Qed.Listset.Make(Filtered)


let tactical_inside step remove =
  let remove = List.sort_uniq Lang.F.compare remove in
  let collect p =
    match Lang.F.p_expr p with
    | And ps -> ps
    | _ -> [ p ]
  in
  begin match step.condition with
    | Type p | Have p | When p | Core p | Init p ->
      let ps = Lang.F.e_props @@ collect p in
      let kept = TermLset.diff ps remove in
      let removed =
        let add s e = Filteredset.add (Filtered.of_term e) s in
        List.fold_left add Filteredset.empty remove
      in
      let feedback =
        let pp fmt f = Format.fprintf fmt "'%a'" Filtered.pretty f in
        Format.asprintf "Filtered: %a"
          (Pretty_utils.pp_list ~sep:", " pp) removed
      in
      let cond = condition step @@ Lang.F.p_bool @@ Lang.F.e_and kept in
      removed, Tactical.replace_single ~at:step.id (feedback, cond)

    | _ -> raise Not_found
  end

module Smap = Qed.Idxmap.Make
    (struct
      type t = step
      let id s = s.id
    end)

let collect_remove m = function
  | Inside(Step step, remove) ->
    let l =
      try Smap.find step m
      with Not_found -> []
    in
    Smap.add step (remove :: l) m
  | _ -> raise Not_found

let fold_selection s seq =
  let m = List.fold_left collect_remove Smap.empty s in
  let tactical s l (acc_rm, seq) =
    let rm, op = tactical_inside s l in
    Filteredset.union rm acc_rm, snd @@ op seq
  in
  let removed, seq = Smap.fold tactical m ([], seq) in
  let feedback =
    let pp fmt f = Format.fprintf fmt "'%a'" Filtered.pretty f in
    Format.asprintf "Filtered: %a"
      (Pretty_utils.pp_list ~sep:", " pp) removed
  in
  feedback, seq


let process (f: sequent -> string * sequent) s = [ f s ]

class clear =
  object(_)
    inherit Tactical.make ~id:"Wp.clear"
        ~title:"Clear"
        ~descr:"Remove Hypothesis"
        ~params:[]

    method select _feedback sel =
      match sel with
      | Clause(Step step) ->
        Applicable(process @@ tactical_step step)
      | Inside(Step step, remove) ->
        begin
          try Applicable(process @@ snd @@ tactical_inside step [remove])
          with Not_found -> Not_applicable
        end
      | Multi es ->
        Applicable (process @@ fold_selection es)
      | _ -> Not_applicable
  end

let tactical = Tactical.export (new clear)
