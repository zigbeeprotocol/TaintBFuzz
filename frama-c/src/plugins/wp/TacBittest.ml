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

(* -------------------------------------------------------------------------- *)
(* --- Helpers                                                            --- *)
(* -------------------------------------------------------------------------- *)

let positive e = F.p_leq F.e_zero e (* 0 <= n *)
let power k = F.e_bigint (Integer.two_power_of_int k)

let lookup_int e =
  let open Qed.Logic in
  match F.repr e with
  | Kint z -> (try Some (Integer.to_int_exn z) with Z.Overflow -> None)
  | _ -> None

let rec lookup_bittest e =
  match F.repr e with
  | Not e -> lookup_bittest e
  | Fun(f,[n;ek]) when List.memq f Cint.f_bits ->
    begin
      match lookup_int ek with
      | Some k when 0 <= k && k < 128 -> Some (n,k)
      | _ -> None
    end
  | _ -> None

(* -------------------------------------------------------------------------- *)
(* --- Bit-Test Range                                                     --- *)
(* -------------------------------------------------------------------------- *)

class bittestrange =
  object
    inherit Tactical.make
        ~id:"Wp.bittestrange"
        ~title:"Bit-Test Range"
        ~descr:"Tighten Bounds with respect to bits"
        ~params:[]

    method select _feedback selection =
      let e = Tactical.selected selection in
      match lookup_bittest e with
      | Some (n,k) ->
        let bit = Cint.bit_test n k in
        let bit_set = F.p_bool bit in
        let bit_clear = F.p_not bit_set in
        let pos = positive n in
        let pk = power k in
        let pk1 = power (succ k) in
        let g_inf = F.p_hyps [pos] (F.p_leq pk n) in
        let g_sup = F.p_hyps [pos;F.p_lt n pk1] (F.p_lt n pk) in
        let name_inf = Printf.sprintf "Bit #%d (inf)" k in
        let name_sup = Printf.sprintf "Bit #%d (sup)" k in
        let at = Tactical.at selection in
        Tactical.Applicable (Tactical.insert ?at [
            name_inf , F.p_and bit_set g_inf ;
            name_sup , F.p_and bit_clear g_sup ;
          ])
      | None -> Tactical.Not_applicable

  end

let tactical = Tactical.export (new bittestrange)
let strategy = Strategy.make tactical ~arguments:[]

(* -------------------------------------------------------------------------- *)
(* --- Auto Bitrange                                                      --- *)
(* -------------------------------------------------------------------------- *)

let rec lookup push step e =
  match F.repr e with
  | And es -> List.iter (lookup push step) es
  | Or es -> List.iter (lookup push step) es
  | Imply (hs,p) -> List.iter (lookup push step) (p::hs)
  | _ ->
    begin
      match lookup_bittest e with
      | None -> ()
      | Some _ ->
        push @@ strategy ~priority:0.3 (Tactical.Inside(step,e))
    end

class autobittestrange : Strategy.heuristic =
  object

    method id = "wp:bittestrange"
    method title = "Auto Bit-Test Range"
    method descr = "Apply Bit-Test Range on bit-tests"

    method search push (seq : Conditions.sequent) =
      Conditions.iter
        (fun step ->
           let p = Conditions.head step |> F.e_prop in
           lookup push (Tactical.Step step) p
        ) (fst seq) ;
      let p = snd seq in
      lookup push (Tactical.Goal p) (F.e_prop p)

  end

let () = Strategy.register (new autobittestrange)
