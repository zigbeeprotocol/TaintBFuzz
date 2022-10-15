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

module DatatypeMessages =
  Datatype.Make_with_collections
    (struct
      include Datatype.Serializable_undefined
      open Log
      type t = event
      let name = "message"
      let reprs =
        [ { evt_kind = Failure;
            evt_plugin = "";
            evt_category = None;
            evt_source = None;
            evt_message = "" } ]
      let mem_project = Datatype.never_any_project
      let hash (e: event)= Hashtbl.hash e
      let compare (e1: event) e2 = Extlib.compare_basic e1 e2
      let equal = Datatype.from_compare
    end)

module Messages =
  State_builder.Queue
    (DatatypeMessages)
    (struct
      let name = "Messages.message_table"
      let dependencies = [ Ast.self ]
    end)
let () = Ast.add_monotonic_state Messages.self

let hooks = ref []
let add_message m =
  begin
    Messages.add m;
    List.iter (fun fn -> fn()) !hooks ;
  end

let nb_errors () =
  Messages.fold
    (fun n e ->
       match e.Log.evt_kind with
       | Log.Error -> succ n
       | _ -> n) 0

let nb_warnings () =
  Messages.fold
    (fun n e ->
       match e.Log.evt_kind with
       | Log.Warning -> succ n
       | _ -> n) 0

let nb_messages = Messages.length

let self = Messages.self

let iter = Messages.iter
let fold = Messages.fold
let dump_messages () = iter Log.echo

let () = Log.add_listener add_message

module OnceTable =
  State_builder.Hashtbl
    (DatatypeMessages.Hashtbl)
    (Datatype.Unit)
    (struct
      let size = 37
      let dependencies = [ Ast.self ]
      let name = "Messages.OnceTable"
    end)

let check_not_yet evt =
  if OnceTable.mem evt then false
  else begin
    OnceTable.add evt ();
    true
  end

let () = Log.check_not_yet := check_not_yet

let reset_once_flag () = OnceTable.clear ()

let add_global_hook fn = hooks := !hooks @ [fn]

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
