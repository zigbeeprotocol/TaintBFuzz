(**************************************************************************)
(*                                                                        *)
(*  This file is part of Aorai plug-in of Frama-C.                        *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*    INRIA (Institut National de Recherche en Informatique et en         *)
(*           Automatique)                                                 *)
(*    INSA  (Institut National des Sciences Appliquees)                   *)
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

let show_aorai_variable state fmt var_name =
  let vi = Data_for_aorai.(get_varinfo var_name) in
  let cvalue = Cvalue.Model.find state (Locations.loc_of_varinfo vi) in
  try
    let i = Ival.project_int (Cvalue.V.project_ival cvalue) in
    let state_name = Data_for_aorai.getStateName (Integer.to_int_exn i) in
    Format.fprintf fmt "%s" state_name
  with Cvalue.V.Not_based_on_null | Ival.Not_Singleton_Int |
       Z.Overflow | Not_found ->
    Format.fprintf fmt "?"

let show_val fmt (expr, v) =
  Format.fprintf fmt "%a in %a"
    Printer.pp_exp expr
    (Cvalue.V.pretty_typ (Some (Cil.typeOf expr))) v

let show_non_det_state fmt state =
  let (states,_) = Data_for_aorai.getGraph () in
  let first_print = ref true in
  let print_state s sure =
    if not !first_print then Format.fprintf fmt ",@ ";
    first_print := false;
    Format.fprintf fmt "%s%s"
      (if sure then "" else "(?)")
      s.Promelaast.name
  in
  let print_one s =
    (* TODO: sync Data_for_aorai.get_state_var with current project*)
    let vi = Data_for_aorai.get_varinfo s.Promelaast.name in
    let e = Cil.evar vi in
    let cvalue = !Db.Value.eval_expr state e in
    if Cvalue.V.contains_non_zero cvalue then
      print_state s (not (Cvalue.V.contains_zero cvalue))
  in
  List.iter print_one states

let show_aorai_state = "Frama_C_show_aorai_state"

let builtin_show_aorai_state state args =
  if not (Aorai_option.Deterministic.get()) then begin
    Aorai_option.result ~current:true
      "@[<hv 2>Possible states:@ %a@]" show_non_det_state state;
  end else begin
    let history = Data_for_aorai.(curState :: (whole_history ())) in
    Aorai_option.result ~current:true "@[<hv>%a@]"
      (Pretty_utils.pp_list ~sep:" <- " (show_aorai_variable state)) history;
  end;
  if args <> [] then begin
    Aorai_option.result ~current:true "@[<hv>%a@]"
      (Pretty_utils.pp_list ~sep:"," show_val) args
  end;
  (* Return value : returns nothing, changes nothing *)
  Eva.Builtins.States [state]

let () =
  Cil_builtins.add_custom_builtin
    (fun () -> (show_aorai_state,Cil.voidType,[],true))

let () =
  Eva.Builtins.register_builtin show_aorai_state Cacheable builtin_show_aorai_state

let add_slevel_annotation vi kind =
  match kind with
  | Aorai_visitors.Aux_funcs.(Pre _ | Post _) ->
    let kf = Globals.Functions.get vi in
    let stmt = Kernel_function.find_first_stmt kf
    and emitter = Aorai_option.emitter in
    Eva.Eva_annotations.(add_slevel_annot ~emitter stmt SlevelFull)
  | _ -> ()

let add_slevel_annotations () =
  Aorai_visitors.Aux_funcs.iter add_slevel_annotation

let add_nondet_partitioning () =
  let (states,_) = Data_for_aorai.getGraph() in
  let add_one_state state =
    let vi = Data_for_aorai.get_state_var state in
    Eva.Parameters.use_global_value_partitioning vi
  in
  List.iter add_one_state states

let add_partitioning varname =
  match Data_for_aorai.get_varinfo_option varname with
  | None -> add_nondet_partitioning ()
  | Some vi -> Eva.Parameters.use_global_value_partitioning vi

let add_aux_partitioning () =
  List.iter
    Eva.Parameters.use_global_value_partitioning
    (Data_for_aorai.aux_variables())

let add_state_variables_partitioning () =
  add_partitioning Data_for_aorai.curState;
  add_aux_partitioning ();
  List.iter add_partitioning (Data_for_aorai.whole_history ())

let setup () =
  add_slevel_annotations ();
  add_state_variables_partitioning ()
