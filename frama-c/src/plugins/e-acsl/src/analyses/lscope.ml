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
open Cil_datatype
open Analyses_types

type t = lscope
(* The logic scope is usually small, so a list is fine instead of a Map *)

let empty = []

let add lscope_var t = lscope_var :: t

let remove lscope_var t =
  List.filter (fun elt -> elt != lscope_var) t

let get_all t = t

let exists lv t =
  let is_lv = function
    | Lvs_let(lv', _) | Lvs_quantif(_, _, lv', _, _) | Lvs_formal(lv', _)
    | Lvs_global(lv', _) ->
      Cil_datatype.Logic_var.equal lv lv'
  in
  List.exists is_lv t

exception Lscope_used
let is_used lscope pot =
  let o = object inherit Visitor.frama_c_inplace
    method !vlogic_var_use lv = match lv.lv_origin with
      | Some _ -> Cil.SkipChildren
      | None -> if exists lv lscope then raise Lscope_used else Cil.SkipChildren
  end
  in
  try
    (match pot with
     | PoT_pred p -> ignore (Visitor.visitFramacPredicate o p)
     | PoT_term t -> ignore (Visitor.visitFramacTerm o t));
    false
  with Lscope_used ->
    true

let rank_lvar = function
  | Lvs_let _ -> 0
  | Lvs_quantif _ -> 1
  | Lvs_formal _ -> 2
  | Lvs_global _ -> 3

let hash_list f = List.fold_left (fun acc d -> 65537 * acc + f d) 1

let pretty_lscope_var fmt lscope_var =
  match lscope_var with
  | Lvs_let (lv, t) ->
    Format.fprintf fmt "@[Lvs_let (%a = %a)@]"
      Printer.pp_logic_var lv
      Printer.pp_term t
  | Lvs_quantif (lt, lr, lv, rr, rt) ->
    Format.fprintf fmt "@[Lvs_quantif (%a %a %a %a %a)@]"
      Printer.pp_term lt
      Printer.pp_relation lr
      Printer.pp_logic_var lv
      Printer.pp_relation rr
      Printer.pp_term rt
  | Lvs_formal (lv, li) ->
    Format.fprintf fmt "@[Lvs_formal (%a, %a)@]"
      Printer.pp_logic_var lv
      Printer.pp_logic_info li
  | Lvs_global (lv, t) ->
    Format.fprintf fmt "@[Lvs_global (%a, %a)@]"
      Printer.pp_logic_var lv
      Printer.pp_term t

module D = Datatype.Make(struct
    type t = lscope

    let name = "E_ACSL.Lscope"

    let reprs =
      let reprs =
        List.fold_left
          (fun reprs lv ->
             List.fold_left
               (fun reprs t -> Lvs_let (lv, t) :: reprs)
               reprs
               Term.reprs)
          []
          Logic_var.reprs
      in
      [ reprs; []]

    include Datatype.Undefined

    let compare lscope1 lscope2 =
      let lscope_vars1 = get_all lscope1 in
      let lscope_vars2 = get_all lscope2 in
      Extlib.list_compare
        (fun lscope_var1 lscope_var2 ->
           let r1 = rank_lvar lscope_var1 in
           let r2 = rank_lvar lscope_var2 in
           if r1 <> r2 then r1 - r2 else
             match lscope_var1, lscope_var2 with
             | Lvs_let (lv1, t1), Lvs_let (lv2, t2) ->
               let c = Logic_var.compare lv1 lv2 in
               if c <> 0 then c else Term.compare t1 t2
             | Lvs_quantif (lt1, lr1, lv1, rr1, rt1),
               Lvs_quantif (lt2, lr2, lv2, rr2, rt2) ->
               let c = Logic_var.compare lv1 lv2 in
               let c =
                 if c <> 0 then c
                 else Term.compare lt1 lt2
               in
               let c =
                 if c <> 0 then c
                 else Term.compare rt1 rt2
               in
               let c =
                 if c <> 0 then c
                 else Stdlib.compare lr1 lr2
               in
               let c =
                 if c <> 0 then c
                 else Stdlib.compare rr1 rr2
               in
               c
             | Lvs_formal (lv1, li1), Lvs_formal (lv2, li2) ->
               let c = Logic_var.compare lv1 lv2 in
               if c <> 0 then c else Logic_info.compare li1 li2
             | Lvs_global (lv1, t1), Lvs_global (lv2, t2) ->
               let c = Logic_var.compare lv1 lv2 in
               if c <> 0 then c else Term.compare t1 t2
             | (Lvs_let _ | Lvs_quantif _ | Lvs_formal _ | Lvs_global _), _ ->
               assert false
        )
        lscope_vars1
        lscope_vars2

    let equal = Datatype.from_compare

    let hash lscope =
      let lscope_vars = get_all lscope in
      hash_list
        (fun lscope_var ->
           match lscope_var with
           | Lvs_let (lv, t) -> 2 * Logic_var.hash lv + 3 * Term.hash t
           | Lvs_quantif (lt, lr, lv, rr, rt) ->
             5 * Logic_var.hash lv
             + 7 * Term.hash lt
             + 11 * Term.hash rt
             + 13 * Hashtbl.hash lr
             + 17 * Hashtbl.hash rr
           | Lvs_formal (lv, li) ->
             19 * Logic_var.hash lv + 23 * Logic_info.hash li
           | Lvs_global (lv, t) ->
             29 * Logic_var.hash lv + 31 * Term.hash t
        )
        lscope_vars

    let pretty fmt lscope =
      let lscope_vars = List.rev lscope in
      Format.fprintf fmt "@[[%a]@]"
        (Pretty_utils.pp_list ~sep:",@ " pretty_lscope_var) lscope_vars
  end)

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
