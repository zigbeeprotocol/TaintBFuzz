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
open Eval

module type InputDomain = sig
  include Datatype.S
  val top: t
  val join: t -> t -> t
end

module type S = sig
  type t
  val register_global_state: bool -> t or_bottom -> unit
  val register_initial_state: Value_types.callstack -> t -> unit
  val register_state_before_stmt: Value_types.callstack -> stmt -> t -> unit
  val register_state_after_stmt: Value_types.callstack -> stmt -> t -> unit

  (** Allows accessing the states inferred by an Eva analysis after it has
      been computed with the domain enabled. *)
  val get_global_state: unit -> t or_bottom
  val get_initial_state: kernel_function -> t or_bottom
  val get_initial_state_by_callstack:
    ?selection:callstack list ->
    kernel_function -> t Value_types.Callstack.Hashtbl.t or_top_bottom

  val get_stmt_state: after:bool -> stmt -> t or_bottom
  val get_stmt_state_by_callstack:
    ?selection:callstack list ->
    after:bool -> stmt -> t Value_types.Callstack.Hashtbl.t or_top_bottom

  val mark_as_computed: unit -> unit
  val is_computed: unit -> bool
end

module Make (Domain: InputDomain) = struct

  let name = Domain.name ^ ".Store"

  (* This module stores the resulting states of an Eva analysis. They depends on
     the set of parameters with which the analysis has been run, and must be
     cleared each time one of this parameter is changed. Thus, the tables of
     this module have as dependencies Self.state, the internal state of Eva
     (all parameters of Eva are added as codependencies of this state).  *)
  let dependencies = [ Self.state ]
  let size = 16

  module type Ref = sig
    val get : unit -> bool
    val set : bool -> unit
  end

  (* Boolean reference saved on the disk. *)
  module Bool_Ref_State =
    State_builder.Ref
      (Datatype.Bool)
      (struct
        let dependencies = dependencies
        let name = name ^ ".Storage"
        let default () = false
      end)

  (* Boolean reference. Not saved on the disk. *)
  module Bool_Ref = struct
    let x = ref false
    let set y = x := y
    let get () = !x
  end

  (* A boolean reference indicating whether the states of the domain have been
     saved. False by default, it becomes true when the engine calls
     [register_global_state] at the start of the analysis.
     If the domain is unmarshallable, its states cannot be saved on the
     disk, and this boolean should not be saved either. *)
  module Storage =
    (val (if Descr.is_unmarshable Domain.descr
          then (module Bool_Ref)
          else (module Bool_Ref_State)) : Ref)

  module Global_State =
    State_builder.Option_ref (Domain)
      (struct
        let dependencies = dependencies
        let name = name ^ ".Global_State"
      end)

  module States_by_callstack =
    Value_types.Callstack.Hashtbl.Make (Domain)

  module Table_By_Callstack =
    Cil_state_builder.Stmt_hashtbl(States_by_callstack)
      (struct
        let name = name ^ ".Table_By_Callstack"
        let size = size
        let dependencies = dependencies
      end)
  module Table =
    Cil_state_builder.Stmt_hashtbl (Domain)
      (struct
        let name = name ^ ".Table"
        let size = size
        let dependencies = [ Table_By_Callstack.self ]
      end)

  module AfterTable_By_Callstack =
    Cil_state_builder.Stmt_hashtbl (States_by_callstack)
      (struct
        let name = name ^ ".AfterTable_By_Callstack"
        let size = size
        let dependencies = dependencies
      end)
  module AfterTable =
    Cil_state_builder.Stmt_hashtbl (Domain)
      (struct
        let name = name ^ ".AfterTable"
        let size = size
        let dependencies = [ AfterTable_By_Callstack.self ]
      end)

  module Called_Functions_By_Callstack =
    State_builder.Hashtbl
      (Kernel_function.Hashtbl)
      (States_by_callstack)
      (struct
        let name = name ^ ".Called_Functions_By_Callstack"
        let size = 11
        let dependencies = dependencies
      end)

  module Called_Functions_Memo =
    State_builder.Hashtbl
      (Kernel_function.Hashtbl)
      (Domain)
      (struct
        let name = name ^ ".Called_Functions_Memo"
        let size = 11
        let dependencies = [ Called_Functions_By_Callstack.self ]
      end)

  let update_callstack_table ~after stmt callstack v =
    let open Value_types in
    let find,add =
      if after
      then AfterTable_By_Callstack.find, AfterTable_By_Callstack.add
      else Table_By_Callstack.find, Table_By_Callstack.add
    in
    try
      let by_callstack = find stmt in
      begin try
          let o = Callstack.Hashtbl.find by_callstack callstack in
          Callstack.Hashtbl.replace by_callstack callstack (Domain.join o v)
        with Not_found ->
          Callstack.Hashtbl.add by_callstack callstack v
      end;
    with Not_found ->
      let r = Callstack.Hashtbl.create 7 in
      Callstack.Hashtbl.add r callstack v;
      add stmt r

  let register_global_state storage state =
    Storage.set storage;
    if storage then
      match state with
      | `Bottom -> ()
      | `Value state -> Global_State.set state

  let register_initial_state callstack state =
    if Storage.get () then
      let open Value_types in
      let kf = match callstack with (kf, _) :: _ -> kf | _ -> assert false in
      let by_callstack =
        try Called_Functions_By_Callstack.find kf
        with Not_found ->
          let h = Callstack.Hashtbl.create 7 in
          Called_Functions_By_Callstack.add kf h;
          h
      in
      try
        let old = Callstack.Hashtbl.find by_callstack callstack in
        Callstack.Hashtbl.replace by_callstack callstack (Domain.join old state)
      with Not_found ->
        Callstack.Hashtbl.add by_callstack callstack state

  let get_global_state () =
    if not (Storage.get ())
    then `Value Domain.top
    else match Global_State.get_option () with
      | None -> `Bottom
      | Some state -> `Value state

  let get_initial_state kf =
    if not (Storage.get ())
    then `Value Domain.top
    else
      try `Value (Called_Functions_Memo.find kf)
      with Not_found ->
      try
        let by_callstack = Called_Functions_By_Callstack.find kf in
        let state =
          Value_types.Callstack.Hashtbl.fold
            (fun _cs state acc -> Bottom.join Domain.join acc (`Value state))
            by_callstack `Bottom
        in
        ignore (state >>-: Called_Functions_Memo.add kf);
        state
      with Not_found -> `Bottom

  let select ?selection tbl =
    match selection with
    | None -> tbl
    | Some list ->
      let new_tbl = Value_types.Callstack.Hashtbl.create (List.length list) in
      let add cs =
        let state_opt = Value_types.Callstack.Hashtbl.find_opt tbl cs in
        Option.iter (Value_types.Callstack.Hashtbl.replace new_tbl cs) state_opt
      in
      List.iter add list;
      new_tbl

  let get_state_by_callstack ?selection find key =
    if not (Storage.get ())
    then `Top
    else
      try `Value (select ?selection (find key))
      with Not_found -> `Bottom

  let get_initial_state_by_callstack ?selection kf =
    get_state_by_callstack ?selection Called_Functions_By_Callstack.find kf

  let get_stmt_state ~after s =
    if not (Storage.get ())
    then `Value Domain.top
    else
      let (find, add), find_by_callstack =
        if after
        then AfterTable.(find, add), AfterTable_By_Callstack.find
        else Table.(find, add), Table_By_Callstack.find
      in
      try `Value (find s)
      with Not_found ->
        let ho = try Some (find_by_callstack s) with Not_found -> None in
        let state =
          match ho with
          | None -> `Bottom
          | Some h ->
            Value_types.Callstack.Hashtbl.fold
              (fun _cs state acc -> Bottom.join Domain.join acc (`Value state))
              h `Bottom
        in
        ignore (state >>-: add s);
        state

  let get_stmt_state_by_callstack ?selection ~after stmt =
    let find =
      if after
      then AfterTable_By_Callstack.find
      else Table_By_Callstack.find
    in
    get_state_by_callstack ?selection find stmt

  let register_state_before_stmt callstack stmt state =
    if Storage.get ()
    then update_callstack_table ~after:false stmt callstack state

  let register_state_after_stmt callstack stmt state =
    if Storage.get ()
    then update_callstack_table ~after:true stmt callstack state

  let mark_as_computed () = Table_By_Callstack.mark_as_computed ()
  let is_computed () = Storage.get () && Table_By_Callstack.is_computed ()
end
