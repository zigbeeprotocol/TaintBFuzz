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

(* -------------------------------------------------------------------------- *)
(* --- Array Dimensions                                                   --- *)
(* -------------------------------------------------------------------------- *)

(* private *)
type t = [ `Fix | `Ext ] list

let of_dims = List.map (function None -> `Ext | Some _ -> `Fix)

let compare (ps : t) (qs : t) = Stdlib.compare ps qs

let rec pp_hdims fmt = function
  | [] -> ()
  | `Fix :: ps -> pp_ndims `Fix 1 fmt ps
  | `Ext :: ps -> pp_ndims `Ext 1 fmt ps

and pp_ndims p k fmt = function
  | q :: qs when p = q -> pp_ndims p (succ k) fmt qs
  | ps -> pp_kdim p k fmt ; pp_hdims fmt ps

and pp_kdim p k fmt =
  begin
    if p = `Fix then Format.pp_print_char fmt 'd' ;
    if p = `Ext then Format.pp_print_char fmt 'w' ;
    if k > 1 then Format.pp_print_int fmt k ;
  end

let pp_suffix_id fmt = function
  | [] | [`Fix] -> ()
  | ps -> Format.pp_print_char fmt '_' ; pp_hdims fmt ps

let pretty fmt ps = pp_hdims fmt ps

(* -------------------------------------------------------------------------- *)
(* --- Compilation Environment                                            --- *)
(* -------------------------------------------------------------------------- *)

open Lang.F

type env = {
  size_var : var list ; (* size variables *)
  size_val : term list ; (* size values *)
  index_var : var list ; (* index variables *)
  index_val : term list ; (* index values *)
  index_range : pred list ; (* indices are in range of size variables *)
  index_offset : term list ; (* polynomial of indices multiplied by previous sizes *)
  length : term option ; (* number of array cells ; None is infinite *)
}

let rec collect rank = function
  | [] ->
    {
      size_var = [] ;
      size_val = [] ;
      index_var = [] ;
      index_val = [] ;
      index_range = [] ;
      index_offset = [] ;
      length = Some e_one ;
    }
  | d::ds ->
    let denv = collect (succ rank) ds in
    let k_base = match rank with 0 -> "i" | 1 -> "j" | _ -> "k" in
    let k_var = Lang.freshvar ~basename:k_base Qed.Logic.Int in
    let k_val = e_var k_var in
    let k_ofs = e_prod (k_val :: denv.size_val) in
    match d with
    | `Ext ->
      { denv with
        index_var = k_var :: denv.index_var ;
        index_val = k_val :: denv.index_val ;
        index_offset = k_ofs :: denv.index_offset ;
        length = None ;
      }
    | `Fix ->
      let n_base = match rank with 0 -> "n" | 1 -> "m" | _ -> "d" in
      let n_var = Lang.freshvar ~basename:n_base Qed.Logic.Int in
      let n_val = e_var n_var in
      let k_inf = p_leq e_zero k_val in
      let k_sup = p_lt k_val n_val in
      let length = match denv.length with
        | None -> None
        | Some len -> Some (e_mul n_val len)
      in {
        size_var = n_var :: denv.size_var ;
        size_val = n_val :: denv.size_val ;
        index_var = k_var :: denv.index_var ;
        index_val = k_val :: denv.index_val ;
        index_offset = k_ofs :: denv.index_offset ;
        index_range = k_inf :: k_sup :: denv.index_range ;
        length ;
      }

let cc_env = collect 0

let rec cc_dims ns =
  match ns with
  | [] -> []
  | Some n :: ns -> e_int n :: cc_dims ns
  | None :: ns -> cc_dims ns

let cc_tau te ds = Lang.t_matrix te (List.length ds)

(* -------------------------------------------------------------------------- *)
(* --- Dimension Merging                                                  --- *)
(* -------------------------------------------------------------------------- *)

let rec do_merge ds1 ds2 =
  match ds1 , ds2 with
  | [] , [] -> []
  | [] , _ | _ , [] -> raise Exit
  | d1::ds1 , d2::ds2 ->
    let d = match d1 , d2 with
      | None , _ | _ , None -> None
      | Some n1 , Some n2 -> if n1=n2 then d1 else raise Exit
    in d :: do_merge ds1 ds2

let merge ds1 ds2 =
  try Some(do_merge ds1 ds2)
  with Exit -> None

(* -------------------------------------------------------------------------- *)
