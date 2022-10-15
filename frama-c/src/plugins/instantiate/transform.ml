(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
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
open Instantiator_builder

let base : (string, (module Instantiator)) Hashtbl.t = Hashtbl.create 17

let register (module G: Generator_sig) =
  let module Instantiator = Make_instantiator(G) in
  Hashtbl.add base G.function_name (module Instantiator)

let get_kfs () =
  let get_kfs _ instantiator =
    let module I = (val instantiator: Instantiator) in
    let res = I.get_kfs () in
    res
  in
  Hashtbl.fold (fun k v l -> (get_kfs k v) @ l) base []

let clear () =
  Global_context.clear () ;
  let clear _ instantiator =
    let module I = (val instantiator: Instantiator) in
    I.clear ()
  in
  Hashtbl.iter clear base

module VISet = Cil_datatype.Varinfo.Hptset

class transformer = object(self)
  inherit Visitor.frama_c_inplace

  val introduced_instantiators = ref VISet.empty
  val used_instantiator_last_kf = Queue.create ()

  method! vfile _ =
    let post f =
      f.globals <- (Global_context.globals (Cil.CurrentLoc.get())) @ f.globals ;
      Ast.mark_as_changed () ;
      Ast.mark_as_grown () ;
      f
    in
    Cil.DoChildrenPost post

  method! vglob_aux _ =
    let post g =
      let loc = Cil.CurrentLoc.get() in
      let folding l fd =
        if VISet.mem fd.svar !introduced_instantiators then l
        else begin
          introduced_instantiators := VISet.add fd.svar !introduced_instantiators ;
          GFun (fd, loc) :: l
        end
      in
      Queue.fold folding g used_instantiator_last_kf
    in
    Cil.DoChildrenPost post

  method! vfunc f =
    let kf = Globals.Functions.get f.svar in
    if not (Options.Kfs.is_set ()) || Options.Kfs.mem kf then
      Cil.DoChildren
    else
      Cil.SkipChildren

  method private find_enabled_instantiator fct =
    let instantiator = Hashtbl.find base fct.vname in
    let module I = (val instantiator: Instantiator) in
    if not (I.Enabled.get ()) then raise Not_found ;
    instantiator

  method private replace_call (lval, fct, args) =
    try
      let module I = (val (self#find_enabled_instantiator fct): Instantiator) in
      if I.well_typed_call lval fct args then
        let key = I.key_from_call lval fct args in
        let fundec = I.get_override key in
        let new_args = I.retype_args key args in
        Queue.add fundec used_instantiator_last_kf ;
        (fundec.svar), new_args
      else begin
        Options.warning
          ~current:true "%s instantiator cannot replace call" fct.vname ;
        (fct, args)
      end
    with
    | Not_found -> (fct, args)

  method! vinst = function
    | Call(_, { enode = Lval((Var _), NoOffset)} , _, _)
    | Local_init(_, ConsInit(_ , _, Plain_func), _) ->
      let change = function
        | [ Call(r, ({ enode = Lval((Var f), NoOffset) } as e), args, loc) ] ->
          let f, args = self#replace_call (r, f, args) in
          [ Call(r, { e with enode = Lval((Var f), NoOffset) }, args, loc) ]
        | [ Local_init(r, ConsInit(f, args, Plain_func), loc) ] ->
          let f, args = self#replace_call (Some (Cil.var r), f, args) in
          [ Local_init(r, ConsInit(f, args, Plain_func), loc) ]
        | _ -> assert false
      in
      Cil.DoChildrenPost change
    | _ -> Cil.DoChildren
end

let validate_property p =
  Property_status.emit Options.emitter ~hyps:[] p Property_status.True

let compute_call_preconditions_statuses kf =
  let stmt = Kernel_function.find_first_stmt kf in
  let _ = Kernel_function.find_all_enclosing_blocks stmt in
  match stmt.skind with
  | Instr (Local_init(_, ConsInit(fct, _, Plain_func), _))
  | Instr (Call(_, { enode = Lval ((Var fct), NoOffset) }, _, _)) ->
    let called_kf = Globals.Functions.get fct in
    Statuses_by_call.setup_all_preconditions_proxies called_kf ;
    let reqs = Statuses_by_call.all_call_preconditions_at
        ~warn_missing:true called_kf stmt
    in
    List.iter (fun (_, p) -> validate_property p) reqs ;
  | _ ->
    Options.fatal "Transformation: unexpected instruction kind on precondition"

let compute_postconditions_statuses kf =
  let posts bhv =
    List.iter validate_property
      (Property.ip_post_cond_of_behavior kf ~active:[] Kglobal bhv)
  in
  Annotations.iter_behaviors (fun _ -> posts) kf

let compute_comp_disj_statuses kf =
  let open Property in
  let comps c = validate_property (ip_of_complete kf Kglobal ~active:[] c) in
  let disjs d = validate_property (ip_of_disjoint kf Kglobal ~active:[] d) in
  Annotations.iter_complete (fun _ -> comps) kf ;
  Annotations.iter_disjoint (fun _ -> disjs) kf

let compute_statuses_all_kfs () =
  let kfs = get_kfs () in
  List.iter compute_call_preconditions_statuses kfs ;
  List.iter compute_postconditions_statuses kfs ;
  List.iter compute_comp_disj_statuses kfs

let transform file =
  clear () ;
  Visitor.visitFramacFile (new transformer) file ;
  File.reorder_ast () ;
  compute_statuses_all_kfs ()
