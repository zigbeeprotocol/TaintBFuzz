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

(* Only Compiled when package Zmq is installed *)
(* No interface, registered via side-effects   *)

(* -------------------------------------------------------------------------- *)
(* --- ZeroMQ Server Options                                              --- *)
(* -------------------------------------------------------------------------- *)

module Senv = Server_parameters

let zmq_group = Senv.add_group "Protocol ZeroMQ"

let () = Parameter_customize.set_group zmq_group
module Socket = Senv.String
    (struct
      let option_name = "-server-zmq"
      let arg_name = "url"
      let default = ""
      let help =
        "Launch the ZeroMQ server (in background).\n\
         The server can handle GET requests during the\n\
         execution of the frama-c command line.\n\
         Finally, the server is executed until shutdown."
    end)

let () = Parameter_customize.set_group zmq_group
module Client = Senv.String
    (struct
      let option_name = "-server-gui"
      let arg_name = "cmd"
      let default = ""
      let help =
        "Launch the ZeroMQ client (as a child process).\n\
         If not started by -server-zmq <url>, the ZeroMQ server\n\
         is established with a local 'ipc://<tmp>' address.\n\
         The specified <cmd> is passed the actual server <url>\n\
         as first and unique argument."
    end)

let _ = Server_doc.protocole ~title:"ZeroMQ Protocol" ~readme:"server_zmq.md"

(* -------------------------------------------------------------------------- *)
(* --- ZMQ Context                                                        --- *)
(* -------------------------------------------------------------------------- *)

let zmq_context =
  let zmq = ref None in
  fun () ->
    match !zmq with
    | Some ctxt -> ctxt
    | None ->
      let major,minor,patch = Zmq.version () in
      Senv.debug "ZeroMQ [v%d.%d.%d]" major minor patch ;
      let ctxt = Zmq.Context.create () in
      at_exit (fun () -> Zmq.Context.terminate ctxt) ;
      zmq := Some ctxt ; ctxt

(* -------------------------------------------------------------------------- *)
(* --- Decoding Requests                                                  --- *)
(* -------------------------------------------------------------------------- *)

exception WrongEncoding of string

let jdecode txt =
  try Yojson.Basic.from_string txt
  with exn ->
    (* Exception if purely local from Yojson *)
    raise (WrongEncoding (Printexc.to_string exn))

let jencode js =
  try Yojson.Basic.to_string ~std:false js
  with exn ->
    (* Exception if purely local from Yojson *)
    raise (WrongEncoding (Printexc.to_string exn))

let rec decode = function
  | ("GET"|"SET"|"EXEC")::id::request::data :: w ->
    `Request(id,request,jdecode data) :: decode w
  | "KILL"::id:: w -> `Kill id :: decode w
  | "SIGON" :: sg :: w -> `SigOn sg :: decode w
  | "SIGOFF" :: sg :: w -> `SigOff sg :: decode w
  | "POLL" :: w -> `Poll :: decode w
  | "SHUTDOWN" :: _ -> [`Shutdown]
  | cmd::_ -> raise (WrongEncoding cmd)
  | [] -> []

let rec encode = function
  | `Data(id,data) :: w -> "DATA" :: id :: jencode data :: encode w
  | `Error(id,msg) :: w -> "ERROR" :: id :: msg :: encode w
  | `Killed id :: w -> "KILLED" :: id :: encode w
  | `Rejected id :: w -> "REJECTED" :: id :: encode w
  | `Signal sg :: w -> "SIGNAL" :: sg :: encode w
  | `CmdLineOn :: w -> "CMDLINEON" :: encode w
  | `CmdLineOff :: w -> "CMDLINEOFF" :: encode w
  | [] -> []

(* -------------------------------------------------------------------------- *)
(* --- ZMQ Messages                                                       --- *)
(* -------------------------------------------------------------------------- *)

let callback socket responses =
  try
    let msg = encode responses in
    Zmq.Socket.send_all socket (if msg = [] then ["NONE"] else msg)
  with WrongEncoding msg ->
    Zmq.Socket.send_all socket [ "WRONG" ; msg ]

let fetch socket () =
  try
    let msg = Zmq.Socket.recv_all ~block:false socket in
    try Some Main.{ requests = decode msg ; callback = callback socket }
    with WrongEncoding msg ->
      Zmq.Socket.send_all socket [ "WRONG" ; msg ] ; None
  with
  | Unix.Unix_error( Unix.EAGAIN , _ , _ ) -> None
  | Zmq.ZMQ_exception(_,msg) -> Senv.fatal "ZeroMQ error: %s" msg

(* -------------------------------------------------------------------------- *)
(* --- Establish the Server                                               --- *)
(* -------------------------------------------------------------------------- *)

let pretty = Format.pp_print_string
let server = ref None
let client = ref None

let ping () =
  match !client with None -> None | Some process ->
  try Some (process ())
  with Unix.Unix_error _ -> None

let launch_server url =
  match !server with
  | Some _ -> ()
  | None ->
    let context = zmq_context () in
    let socket = Zmq.Socket.(create context rep) in
    try
      Zmq.Socket.bind socket url ;
      Senv.debug "ZeroMQ [%s]" url ;
      let srv = Main.create ~pretty ~fetch:(fetch socket) () in
      server := Some(url,srv) ;
      Extlib.safe_at_exit begin fun () ->
        Main.stop srv ;
        Zmq.Socket.close socket ;
        server := None ;
      end ;
      Main.start srv ;
      Cmdline.at_normal_exit (fun () -> Main.run srv) ;
    with exn ->
      Zmq.Socket.close socket ;
      raise exn

let temp_url () =
  let socket = Filename.temp_file "frama-c.socket" ".io" in
  Extlib.safe_at_exit (fun () -> Extlib.safe_remove socket) ;
  "ipc://" ^ socket

let start_server () =
  match !server with
  | None ->
    let socket = Socket.get () in
    let url = if socket = "" then temp_url () else socket in
    launch_server url ; url
  | Some (url,_) -> url

let launch_client cmd =
  match !client with
  | Some _ -> ()
  | None ->
    begin
      let url = start_server () in
      let process = Command.command_async cmd [| url |] in
      Senv.debug "%s --connect %s@." cmd url ;
      Senv.feedback "Client launched." ;
      client := Some process ;
      Extlib.safe_at_exit
        begin fun () ->
          match ping () with
          | Some (Not_ready kill) ->
            Senv.feedback "Client interrupted." ;
            kill ()
          | _ -> ()
        end ;
    end

let cmdline () =
  begin
    let url = Socket.get () in
    if url <> "" then launch_server url ;
    let cmd = Client.get () in
    if cmd <> "" then launch_client cmd ;
  end

let () = Db.Main.extend cmdline

(* -------------------------------------------------------------------------- *)
