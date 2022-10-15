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
open Basic_blocks

module type Generator_sig = sig
  module Hashtbl: Datatype.Hashtbl
  type override_key = Hashtbl.key

  val function_name: string
  val well_typed_call: lval option -> varinfo -> exp list -> bool
  val key_from_call: lval option -> varinfo -> exp list -> override_key
  val retype_args: override_key -> exp list -> exp list
  val args_for_original: override_key -> exp list -> exp list
  val generate_prototype: override_key -> (string * typ)
  val generate_spec: override_key -> location -> fundec -> funspec
end

module type Instantiator = sig
  module Enabled: Parameter_sig.Bool
  type override_key

  val function_name: string
  val well_typed_call: lval option -> varinfo -> exp list -> bool
  val key_from_call: lval option -> varinfo -> exp list -> override_key
  val retype_args: override_key -> exp list -> exp list
  val get_override: override_key -> fundec
  val get_kfs: unit -> kernel_function list
  val clear: unit -> unit
end

let build_body caller callee args_generator =
  let loc  = Cil_datatype.Location.unknown in
  let ret_var = match Cil.getReturnType caller.svar.vtype with
    | t when Cil.isVoidType t -> None
    | t -> Some (Cil.makeLocalVar caller "__retres" t)
  in
  let call =
    let args = List.map Cil.evar caller.sformals in
    let args = args_generator args in
    Cil.mkStmt (Instr(call_function (Option.map Cil.var ret_var) callee args))
  in
  let ret = Cil.mkStmt (Return (Option.map Cil.evar ret_var, loc)) in
  { (Cil.mkBlock [call ; ret]) with blocals = Option.to_list ret_var }

module Make_instantiator (G: Generator_sig) = struct
  include G
  module Enabled = Options.NewInstantiator (G)
  module Cache = struct
    let tbl = G.Hashtbl.create 13
    let find = G.Hashtbl.find tbl
    let add = G.Hashtbl.add tbl
    let fold f = G.Hashtbl.fold f tbl
    let clear () = G.Hashtbl.clear tbl
  end

  let make_fundec key =
    let open Globals.Functions in
    let (name, typ) = G.generate_prototype key in
    let fd = Basic_blocks.prepare_definition name typ in
    let orig = get_vi (find_by_name function_name) in
    let sbody = build_body fd orig (G.args_for_original key) in
    let fd = { fd with sbody } in
    Cfg.cfgFun fd ;
    fd

  let build_function key =
    let loc = Cil_datatype.Location.unknown in
    let fd = make_fundec key in
    let spec = Cil.empty_funspec () in
    Globals.Functions.replace_by_definition spec fd loc ;
    let kf = Globals.Functions.get fd.svar in
    let spec = generate_spec key loc fd in
    Annotations.add_behaviors Options.emitter kf spec.spec_behavior ;
    List.iter
      (Annotations.add_complete Options.emitter kf)
      spec.spec_complete_behaviors ;
    List.iter
      (Annotations.add_disjoint Options.emitter kf)
      spec.spec_disjoint_behaviors ;
    fd

  let get_override key =
    try
      Cache.find key
    with Not_found ->
      let fd = build_function key in
      Cache.add key fd ;
      fd

  (* If you use this before finalization, you'll have problems *)
  let get_kfs () =
    Cache.fold (fun _ fd l -> Globals.Functions.get fd.svar :: l) []

  let clear () =
    Cache.clear ()
end
