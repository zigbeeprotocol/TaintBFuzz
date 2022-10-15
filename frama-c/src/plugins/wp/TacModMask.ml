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

let title_no_revert = "Revert (current: a & m -> a % m+1)"
let title_revert = "Revert (current: m & a -> a % m+1)"

let v_revert,p_revert =
  Tactical.checkbox ~id:"Wp.modmask.revert"
    ~title:title_no_revert
    ~descr:"Changes operands for modulo"
    ~default:false ()

class modmask =
  object(self)
    inherit Tactical.make
        ~id:"Wp.modmask"
        ~title:"Mod-Mask"
        ~descr:"Converts modulo from/to bitmask"
        ~params:[p_revert]

    method select feedback selection =
      let open Lang.N in
      let open Lang.F in
      let open Qed.Logic in

      let e = Tactical.selected selection in
      let at = Tactical.at selection in

      let on_cond = Tactical.condition in
      let replace_with d v = Tactical.rewrite ?at [ d, Lang.F.p_true, e, v ] in

      let update_title ~hard =
        feedback#set_title "Mod-Mask%s" (if hard then " (hard)" else "")
      in
      let update_field ~enabled =
        let revert = self#get_field v_revert in
        let title = if revert then title_revert else title_no_revert in
        feedback#update_field ~enabled v_revert ;
        feedback#update_field ~title v_revert
      in
      let update_display ~hard ~active_field =
        update_title ~hard ;
        update_field ~enabled:active_field
      in
      match Lang.F.repr e with
      | Mod(a, m) ->
        begin
          try
            let m = Cint.l_lsl e_one @@ Cint.match_power2 m in
            let n = Cint.l_and a (m - e_one) in
            let cond = a >= e_zero in

            update_display ~hard:false ~active_field:false ;
            Applicable (on_cond "Mask Guard" cond @@ replace_with "Mask" n)

          with Not_found ->
            let power_of_2 =
              let v = Lang.freshvar ~basename:"n" Lang.t_int in
              let tv = e_var v in
              p_exists [v] (e_zero <= tv && m = Cint.l_lsl e_one tv)
            in
            let cond = (a >= e_zero && e_zero < m && power_of_2) in
            let n = Cint.l_and a (m - e_one) in

            update_display ~hard:true ~active_field:false ;
            Applicable (on_cond "Mask Guard" cond @@ replace_with "Mask" n)
        end

      | Fun( f , [ a ; b ] ) when Lang.Fun.equal f Cint.f_land ->
        begin
          try
            let a, m =
              try b, Cint.match_power2_minus1 a
              with Not_found -> a, Cint.match_power2_minus1 b
            in

            let cond = a >= e_zero in
            let n = a mod (Cint.l_lsl e_one m) in

            update_display ~hard:false ~active_field:false ;
            Applicable (on_cond "Mod Guard" cond @@ replace_with "Mod" n)

          with Not_found ->
            let a, m = if self#get_field v_revert then b, a else a, b in
            let plus_1_power_of_2 =
              let v = Lang.freshvar ~basename:"n" Lang.t_int in
              let tv = e_var v in
              p_exists [v] (e_zero <= tv && m + e_one = Cint.l_lsl e_one tv)
            in
            let cond = (a >= e_zero && e_zero <= m && plus_1_power_of_2) in
            let n = a mod (m + e_one) in

            update_display ~hard:true ~active_field:true ;
            Applicable (on_cond "Mod Guard" cond @@ replace_with "Mod" n)
        end

      | _ ->
        update_display ~hard:false ~active_field:false ;
        Not_applicable
  end

let modmask = Tactical.export (new modmask)
