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

open Cil_types

module Completeness = struct
  module KfParam = struct
    include Cil_datatype.Kf
    let label = None
  end

  module Data =
    Datatype.Pair
      (Datatype.Bool)
      (Datatype.Function(KfParam)(Datatype.Unit))

  include State_builder.Hashtbl
      (Cil_datatype.Kf.Hashtbl)
      (Data)
      (struct
        let name = "RefUsage.AssignsCompleteness.Callbacks"
        let size = 17
        let dependencies = [ Ast.self ]
      end)
end

exception Incomplete_assigns of (string list * string)

let wkey_pedantic = Wp_parameters.register_warn_category "pedantic-assigns"

type ('a, 'b) result = Ok of 'a | Error of 'b

let collect_assigns kf =
  let opt_try f p = function None -> f p | Some x -> Some x in
  let fold_assigns bhv =
    let folder _ a acc = match a, acc with
      | WritesAny, _ -> None
      | _, None      -> Some a
      | _, Some acc  -> Some (Logic_utils.concat_assigns acc a)
    in
    Annotations.fold_assigns folder kf bhv None
  in
  let find_default () =
    match fold_assigns Cil.default_behavior_name with
    | None -> None
    | Some x -> Some [x]
  in
  let incompletes = ref [] in
  let find_complete () =
    let fold_behaviors names =
      let folder l name = match (fold_assigns name) with
        | None -> raise (Incomplete_assigns(names, name))
        | Some a -> a :: l
      in
      try Some (List.fold_left folder [] names)
      with Incomplete_assigns(bhv_l,b) ->
        incompletes := (bhv_l, b) :: !incompletes ;
        None
    in
    Annotations.fold_complete (fun _ -> opt_try fold_behaviors) kf None
  in
  (* First:
     - try to find default behavior assigns, if we cannot get it
     - try to find a "complete behaviors" set where each behavior has assigns
       As assigns and froms are over-approximations, the result (if it exists)
       must cover all assigned memory locations and all data dependencies.
  *)
  match opt_try find_complete () (opt_try find_default () None) with
  | None -> Error !incompletes
  | Some r -> Ok r

let pretty_behaviors_errors fmt l =
  let pp_complete =
    Pretty_utils.pp_list ~pre:"{" ~suf:"}" ~sep:", " Format.pp_print_string
  in
  let pp_bhv_error fmt (bhv_l, name) =
    Format.fprintf fmt
      "- in complete behaviors: %a@\n  No assigns for (at least) '%s'@\n"
      pp_complete bhv_l name
  in
  match l with
  | [] -> Format.fprintf fmt ""
  | l -> Format.fprintf fmt "%a" (Pretty_utils.pp_list pp_bhv_error) l

let check_assigns kf assigns =
  let complete = (true, fun _ -> ()) in
  let incomplete (_status, current) warning =
    let new_warning kf =
      current kf ;
      warning kf ;
    in
    (false, new_warning)
  in
  let vassigns acc a =
    let res_t = Kernel_function.get_return_type kf in
    let assigns_result ({ it_content=t }, _) = Logic_utils.is_result t in
    let froms = match a with WritesAny -> [] | Writes l -> l in
    let acc =
      if Cil.isPointerType res_t && not (List.exists assigns_result froms) then
        incomplete acc
          begin fun kf ->
            Wp_parameters.warning ~wkey:wkey_pedantic
              ~once:true ~source:(fst (Kernel_function.get_location kf))
              "No 'assigns \\result \\from ...' specification for function '%a'\
               returning pointer type.@ Callers assumptions might be imprecise."
              Kernel_function.pretty kf ;
          end
      else acc
    in
    let vfrom acc = function
      | t, FromAny when Logic_typing.is_pointer_type t.it_content.term_type ->
        incomplete acc
          begin fun _kf ->
            Wp_parameters.warning ~wkey:wkey_pedantic
              ~once:true ~source:(fst t.it_content.term_loc)
              "No \\from specification for assigned pointer '%a'.@ \
               Callers assumptions might be imprecise."
              Cil_printer.pp_identified_term t
          end
      | _ -> acc
    in List.fold_left vfrom acc froms
  in
  match assigns with
  | Error l ->
    false,
    begin fun kf ->
      Wp_parameters.warning ~wkey:wkey_pedantic
        ~once:true ~source:(fst (Kernel_function.get_location kf))
        "No 'assigns' specification for function '%a'.@\n%a\
         Callers assumptions might be imprecise."
        Kernel_function.pretty kf
        pretty_behaviors_errors l
    end
  | Ok l ->
    List.fold_left vassigns complete l

let memo_compute kf =
  Completeness.memo (fun kf -> check_assigns kf (collect_assigns kf)) kf

let compute kf =
  ignore (memo_compute kf)

let is_complete kf =
  fst(memo_compute kf)

let warn kf =
  snd(memo_compute kf) kf
