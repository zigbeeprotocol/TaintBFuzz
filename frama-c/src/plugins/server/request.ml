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

open Package

module Senv = Server_parameters
module Jutil = Yojson.Basic.Util

(* -------------------------------------------------------------------------- *)
(* --- Request Registry                                                   --- *)
(* -------------------------------------------------------------------------- *)

type json = Data.json
type kind = [ `GET | `SET | `EXEC ]

module type Input =
sig
  type t
  val jtype : jtype
  val of_json : json -> t
end

module type Output =
sig
  type t
  val jtype : jtype
  val to_json : t -> json
end

type 'a input = (module Input with type t = 'a)
type 'a output = (module Output with type t = 'a)

(* -------------------------------------------------------------------------- *)
(* --- Signals                                                            --- *)
(* -------------------------------------------------------------------------- *)

type signal = Main.signal

let signal ~package ~name ~descr =
  let id = Package.declare_id ~package ~name ~descr D_signal in
  Main.signal (Package.name_of_ident id)

let emit = Main.emit
let on_signal = Main.on_signal

(* -------------------------------------------------------------------------- *)
(* --- Multiple Fields Requests                                           --- *)
(* -------------------------------------------------------------------------- *)

module Fmap = Map.Make(String)

type rq = {
  mutable param : json Fmap.t ;
  mutable result : json Fmap.t ;
}

let fmap_of_json r js =
  List.fold_left
    (fun r (fd,js) -> Fmap.add fd js r)
    r (Jutil.to_assoc js)

let fmap_to_json r =
  `Assoc (Fmap.fold (fun fd js r -> (fd,js)::r) r [])

type 'a param = rq -> 'a
type 'a result = rq -> 'a -> unit

(* -------------------------------------------------------------------------- *)
(* --- Input/Output Request Processing                                    --- *)
(* -------------------------------------------------------------------------- *)

type _ rq_input =
  | Pnone
  | Pdata : 'a input -> 'a rq_input
  | Pfields : fieldInfo list -> unit rq_input

type _ rq_output =
  | Rnone
  | Rdata : 'a output -> 'a rq_output
  | Rfields : fieldInfo list -> unit rq_output

(* json input syntax *)
let rq_input (type a) (input : a rq_input) : paramInfo =
  match input with
  | Pnone -> assert false
  | Pdata d -> let module D = (val d) in P_value D.jtype
  | Pfields fds -> P_named fds

(* json output syntax *)
let rq_output (type b) (output : b rq_output) : paramInfo =
  match output with
  | Rnone -> assert false
  | Rdata d -> let module D = (val d) in P_value D.jtype
  | Rfields fds -> P_named fds

(* -------------------------------------------------------------------------- *)
(* --- Multi-Parameters Requests                                          --- *)
(* -------------------------------------------------------------------------- *)

type ('a,'b) signature = {
  mutable defined : bool ;
  mutable defaults : json Fmap.t ;
  mutable required : string list ;
  mutable input : 'a rq_input ;
  mutable output : 'b rq_output ;
}

let failure_missing fmap name =
  Data.failure ~json:(fmap_to_json fmap) "Missing parameter '%s'" name

let check_required fmap fd =
  if not (Fmap.mem fd fmap) then failure_missing fmap fd

(* -------------------------------------------------------------------------- *)
(* --- Named Input Parameters Definitions                                 --- *)
(* -------------------------------------------------------------------------- *)

(* current input fields *)
let fds_input s : fieldInfo list =
  if s.defined then
    raise (Invalid_argument "Server.Request: already published");
  match s.input with
  | Pdata _ ->
    raise (Invalid_argument "Server.Request: request has not named input");
  | Pnone -> []
  | Pfields fds -> fds

let param (type a b) (s : (unit,b) signature) ~name ~descr
    ?default (input : a input) : a param =
  let module D = (val input) in
  let ftype = if default = None then D.jtype else Joption D.jtype in
  let fd = Package.{
      fd_name = name ;
      fd_type = ftype ;
      fd_descr = descr ;
    } in
  s.input <- Pfields (fd :: fds_input s) ;
  fun rq ->
    try D.of_json (Fmap.find name rq.param)
    with Not_found ->
    match default with
    | None -> failure_missing rq.param name
    | Some v -> v

let param_opt (type a b) (s : (unit,b) signature) ~name ~descr
    (input : a input) : a option param =
  let module D = (val input) in
  let fd = Package.{
      fd_name = name ;
      fd_type = Joption D.jtype ;
      fd_descr = descr ;
    } in
  s.input <- Pfields (fd :: fds_input s) ;
  fun rq ->
    try Some(D.of_json (Fmap.find name rq.param))
    with Not_found -> None

(* -------------------------------------------------------------------------- *)
(* --- Named Output Parameters Definitions                                --- *)
(* -------------------------------------------------------------------------- *)

(* current output fields *)
let fds_output s : fieldInfo list =
  if s.defined then
    raise (Invalid_argument "Server.Request: already published");
  match s.output with
  | Rdata _ ->
    raise (Invalid_argument "Server.Request: request has not named input");
  | Rnone -> []
  | Rfields fds -> fds

let result (type a b) (s : (a,unit) signature) ~name ~descr
    ?default (output : b output) : b result =
  let module D = (val output) in
  let fd = Package.{
      fd_name = name ;
      fd_type = D.jtype ;
      fd_descr = descr ;
    } in
  s.output <- Rfields (fd :: fds_output s) ;
  begin
    match default with
    | None -> s.required <- name :: s.required
    | Some v -> s.defaults <- Fmap.add name (D.to_json v) s.defaults
  end ;
  fun rq v -> rq.result <- Fmap.add name (D.to_json v) rq.result

let result_opt (type a b) (s : (a,unit) signature) ~name ~descr
    (output : b output) : b option result =
  let module D = (val output) in
  let fd = Package.{
      fd_name = name ;
      fd_type = Joption D.jtype ;
      fd_descr = descr ;
    } in
  s.output <- Rfields (fd :: fds_output s) ;
  fun rq opt ->
    match opt with None -> () | Some v ->
      rq.result <- Fmap.add name (D.to_json v) rq.result

(* -------------------------------------------------------------------------- *)
(* --- Opened Signature Definition                                        --- *)
(* -------------------------------------------------------------------------- *)

let signature ?input ?output () =
  let input = match input with None -> Pnone | Some d -> Pdata d in
  let output = match output with None -> Rnone | Some d -> Rdata d in
  {
    defaults = Fmap.empty ; required = [] ;
    input ; output ; defined = false ;
  }

(* -------------------------------------------------------------------------- *)
(* --- Opened Signature Process                                           --- *)
(* -------------------------------------------------------------------------- *)

(* json input processing *)
let mk_input (type a) name defaults (input : a rq_input) : (rq -> json -> a) =
  match input with
  | Pnone -> Senv.fatal "No input defined for request '%s'" name
  | Pdata d ->
    let module D = (val d) in
    begin fun rq js ->
      rq.result <- defaults ;
      try D.of_json js
      with Jutil.Type_error (msg, js) -> Data.failure_from_type_error msg js
    end
  | Pfields _ ->
    begin fun rq js ->
      try rq.param <- fmap_of_json rq.param js
      with Jutil.Type_error (msg, js) -> Data.failure_from_type_error msg js
    end

(* json output processing *)
let mk_output (type b) name required (output : b rq_output) : (rq -> b -> json) =
  match output with
  | Rnone -> Senv.fatal "No output defined for request '%s'" name
  | Rdata d ->
    let module D = (val d) in (fun _rq v -> D.to_json v)
  | Rfields _ ->
    (fun rq () ->
       List.iter (check_required rq.result) required ;
       fmap_to_json rq.result)

let register_sig (type a b)
    ~package ~kind ~name ~descr ?(signals=[])
    (s : (a,b) signature) (process : rq -> a -> b) =
  if s.defined then
    Senv.fatal "Request '%s' is defined twice" name ;
  let input = mk_input name s.defaults s.input in
  let output = mk_output name s.required s.output in
  let processor js =
    let rq = { param = Fmap.empty ; result = Fmap.empty } in
    js |> input rq |> process rq |> output rq
  in
  let request = D_request {
      rq_kind = kind ;
      rq_input = rq_input s.input ;
      rq_output = rq_output s.output ;
      rq_signals = List.map Main.signal_name signals ;
    } in
  let id = declare_id ~package ~name ~descr request in
  Main.register kind (name_of_ident id) processor ;
  s.defined <- true

(* -------------------------------------------------------------------------- *)
(* --- Request Registration                                               --- *)
(* -------------------------------------------------------------------------- *)

let register ~package ~kind ~name ~descr ?signals ~input ~output process =
  register_sig  ~package ~kind ~name ~descr ?signals
    (signature ~input ~output ())
    (fun _rq v -> process v)

let dictionary (type a) ~package ~name ~descr (d : a Data.Enum.dictionary) =
  let open Data in
  let data = Enum.publish ~package ~name ~descr d in
  let descr = Markdown.plain "Registered tags for the above type." in
  let name = name ^ "Tags" in
  register ~kind:`GET ~package
    ~name ~descr
    ~input:(module Junit)
    ~output:(module Jlist(Tag))
    (fun () -> Enum.tags d) ;
  data

(* -------------------------------------------------------------------------- *)
