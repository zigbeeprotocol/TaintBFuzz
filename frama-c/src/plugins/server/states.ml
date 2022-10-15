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

open Data

type 'a callback = ('a -> unit) -> unit

let install signal hook = function
  | None -> ()
  | Some add_hook ->
    let once = ref true in
    let install ok =
      if ok && !once then
        begin
          once := false ;
          add_hook hook ;
        end
    in Request.on_signal signal install

let install_emit signal add_hook =
  install signal (fun _ -> Request.emit signal) add_hook

(* -------------------------------------------------------------------------- *)
(* --- Values                                                             --- *)
(* -------------------------------------------------------------------------- *)

let register_value (type a) ~package ~name ~descr
    ~(output : a Request.output) ~get
    ?(add_hook : 'b callback option) ()
  =
  let open Markdown in
  let href = link ~name () in
  let module D = (val output) in
  let id = Package.declare_id
      ~package ~name ~descr (D_value D.jtype) in
  let signal = Request.signal
      ~package ~name:(Package.Derived.signal id).name
      ~descr:(plain "Signal for state" @ href) in
  let () = Request.register
      ~package ~name:(Package.Derived.getter id).name
      ~descr:(plain "Getter for state" @ href)
      ~kind:`GET ~input:(module Junit) ~output get in
  install_emit signal add_hook ;
  signal

(* -------------------------------------------------------------------------- *)
(* --- States                                                             --- *)
(* -------------------------------------------------------------------------- *)

let register_state (type a) ~package ~name ~descr
    ~(data : a data) ~get ~set
    ?(add_hook : 'b callback option) () =
  let open Markdown in
  let module D = (val data) in
  let href = link ~name () in
  let id = Package.declare_id
      ~package ~name ~descr (D_state D.jtype) in
  let signal = Request.signal
      ~package ~name:(Package.Derived.signal id).name
      ~descr:(plain "Signal for state" @ href) in
  let () = Request.register
      ~package ~name:(Package.Derived.getter id).name
      ~descr:(plain "Getter for state" @ href)
      ~kind:`GET ~input:(module Junit) ~output:(module D) get in
  let () = Request.register
      ~package ~name:(Package.Derived.setter id).name
      ~descr:(plain "Setter for state" @ href)
      ~kind:`SET ~input:(module D) ~output:(module Junit) set in
  install_emit signal add_hook ;
  signal

(* -------------------------------------------------------------------------- *)
(* --- Model Signature                                                    --- *)
(* -------------------------------------------------------------------------- *)

type 'a column = Package.fieldInfo * ('a -> json option)

type 'a model = 'a column list ref

let model () = ref []

let mkfield (model : 'a model) fd (js : 'a -> json option) =
  let open Package in
  let name = fd.fd_name in
  if List.exists (fun (fd,_) -> fd.fd_name = name) !model then
    raise (Invalid_argument "Server.States.column: duplicate name") ;
  model := (fd , js) :: !model

let column (type a b) ~name ~descr
    ~(data: b Request.output)
    ~(get : a -> b)
    ?(default: b option)
    (model : a model) =
  let module D = (val data) in
  match default with
  | None ->
    let fd = Package.{
        fd_name = name ;
        fd_type = D.jtype ;
        fd_descr = descr ;
      } in
    mkfield model fd (fun a -> Some (D.to_json (get a)))
  | Some d ->
    let fd = Package.{
        fd_name = name ;
        fd_type = Joption D.jtype ;
        fd_descr = descr ;
      } in
    mkfield model fd (fun a ->
        let v = get a in
        if v = d then None else Some (D.to_json v)
      )

let option (type a b) ~name ~descr
    ~(data: b Request.output) ~(get : a -> b option) (model : a model) =
  let module D = (val data) in
  let fd = Package.{
      fd_name = name ;
      fd_type = Joption D.jtype ;
      fd_descr = descr ;
    } in
  mkfield model fd (fun a -> match get a with
      | None -> None
      | Some b -> Some (D.to_json b))

module Kmap = Map.Make(String)

(* -------------------------------------------------------------------------- *)
(* --- Model Content                                                      --- *)
(* -------------------------------------------------------------------------- *)

type 'a update = Remove | Add of 'a
type 'a content = {
  mutable cleared : bool ;
  mutable updates : 'a update Kmap.t ;
}

type 'a array = {
  signal : Request.signal ;
  fkey : string ;
  key : 'a -> string ;
  iter : ('a -> unit) -> unit ;
  getter : (string * ('a -> json option)) list ;
  (* [LC+JS]
     The two following fields allow to keep an array in sync
     with the current project and still have a polymorphic data type. *)
  mutable current : 'a content option ; (* fast access to current project *)
  projects : (string , 'a content) Hashtbl.t ; (* indexed by project *)
}

let synchronize array =
  begin
    Project.register_after_set_current_hook
      ~user_only:false (fun _ -> array.current <- None) ;
    let cleanup p =
      Hashtbl.remove array.projects (Project.get_unique_name p) in
    Project.register_before_remove_hook cleanup ;
    Project.register_todo_before_clear cleanup ;
    Request.on_signal array.signal
      (fun _ ->
         array.current <- None ;
         Hashtbl.clear array.projects ;
      );
  end

let content array =
  match array.current with
  | Some w -> w
  | None ->
    let prj = Project.(current () |> get_unique_name) in
    let content =
      try Hashtbl.find array.projects prj
      with Not_found ->
        let w = {
          cleared = true ;
          updates = Kmap.empty ;
        } in
        Hashtbl.add array.projects prj w ; w
    in
    array.current <- Some content ;
    Request.emit array.signal ;
    content

let reload array =
  let m = content array in
  m.cleared <- true ;
  m.updates <- Kmap.empty ;
  Request.emit array.signal

let update array k =
  let m = content array in
  if not m.cleared then
    m.updates <- Kmap.add (array.key k) (Add k) m.updates ;
  Request.emit array.signal

let remove array k =
  let m = content array in
  if not m.cleared then
    m.updates <- Kmap.add (array.key k) Remove m.updates ;
  Request.emit array.signal

let signal array = array.signal

(* -------------------------------------------------------------------------- *)
(* --- Fetch Model Updates                                                --- *)
(* -------------------------------------------------------------------------- *)

type buffer = {
  reload : bool ;
  mutable capacity : int ;
  mutable pending : int ;
  mutable removed : string list ;
  mutable updated : json list ;
}

let add_entry buffer cols fkey key v =
  let fjs = List.fold_left (fun fjs (fd,to_json) ->
      match to_json v with
      | Some js -> (fd , js) :: fjs
      | None | exception Not_found -> fjs
    ) [] cols in
  let row = (fkey, `String key) :: fjs in
  buffer.updated <- `Assoc row :: buffer.updated ;
  buffer.capacity <- pred buffer.capacity

let remove_entry buffer key =
  buffer.removed <- key :: buffer.removed ;
  buffer.capacity <- pred buffer.capacity

let update_entry buffer cols fkey key = function
  | Remove -> remove_entry buffer key
  | Add v -> add_entry buffer cols fkey key v

let fetch array n =
  let m = content array in
  let reload = m.cleared in
  let buffer = {
    reload ;
    capacity = n ;
    pending = 0 ;
    removed = [] ;
    updated = [] ;
  } in
  begin
    if reload then
      begin
        m.cleared <- false ;
        array.iter
          begin fun v ->
            let key = array.key v in
            if buffer.capacity > 0 then
              add_entry buffer array.getter array.fkey key v
            else
              ( m.updates <- Kmap.add key (Add v) m.updates ;
                buffer.pending <- succ buffer.pending ) ;
          end ;
      end
    else
      m.updates <- Kmap.filter
          begin fun key upd ->
            if buffer.capacity > 0 then
              ( update_entry buffer array.getter array.fkey key upd ; false )
            else
              ( buffer.pending <- succ buffer.pending ; true )
          end m.updates ;
  end ;
  buffer

(* -------------------------------------------------------------------------- *)
(* --- Signature Registry                                                 --- *)
(* -------------------------------------------------------------------------- *)

let rec is_keyType = function
  | Package.Junion js -> List.for_all is_keyType js
  | Jstring | Jalpha | Jkey _ | Jtag _ -> true
  | _ -> false

let register_array ~package ~name ~descr ~key
    ?(keyName="key")
    ?(keyType=Package.Jkey name)
    ~(iter : 'a callback)
    ?(add_update_hook : 'a callback option)
    ?(add_remove_hook : 'a callback option)
    ?(add_reload_hook : unit callback option)
    (model : 'a model) =
  let open Markdown in
  let href = link ~name () in
  let columns = List.rev !model in
  begin
    if List.exists (fun (fd,_) -> fd.Package.fd_name = keyName) columns then
      raise (Invalid_argument (
          Printf.sprintf "States.array(%S) : invalid key %S"
            name keyName
        ));
    if not (is_keyType keyType) then
      raise (Invalid_argument (
          Printf.sprintf "States.array(%S): invalid key type" name
        ));
  end ;
  let fields = Package.{
      fd_name = keyName ;
      fd_type = keyType ;
      fd_descr = plain "Entry identifier." ;
    } :: List.map fst columns in
  let id = Package.declare_id ~package:package ~name:name ~descr
      (D_array { arr_key = keyName ; arr_kind = keyType }) in
  let signal = Request.signal
      ~package ~name:(Package.Derived.signal id).name
      ~descr:(plain "Signal for array" @ href) in
  let row = Package.declare_id
      ~package ~name:(Package.Derived.data id).name
      ~descr:(plain "Data for array rows" @ href)
      (D_record fields) in
  let fs = List.map Package.field fields in
  Data.derived ~package ~id:row (Jrecord fs) ;
  let getter =
    List.map Package.(fun (fd,to_js) -> fd.fd_name , to_js) !model in
  let array = {
    fkey = keyName ; key ; iter ; getter ; signal ;
    current = None ; projects = Hashtbl.create 0
  } in
  let signature = Request.signature ~input:(module Jint) () in
  let module Jkeys = Jlist(struct
      include Jstring
      let jtype = keyType
    end) in
  let module Jrows = Jlist (struct
      include Jany
      let jtype = Package.Jdata row
    end) in
  let set_reload = Request.result signature
      ~name:"reload" ~descr:(plain "array fully reloaded")
      (module Jbool) in
  let set_removed = Request.result signature
      ~name:"removed" ~descr:(plain "removed entries")
      (module Jkeys) in
  let set_updated = Request.result signature
      ~name:"updated" ~descr:(plain "updated entries")
      (module Jrows) in
  let set_pending = Request.result signature
      ~name:"pending" ~descr:(plain "remaining entries to be fetched")
      (module Jint) in
  Request.register_sig
    ~package ~name:(Package.Derived.fetch id).name
    ~descr:(plain "Data fetcher for array" @ href)
    ~kind:`GET signature
    begin fun rq n ->
      let buffer = fetch array n in
      set_reload rq buffer.reload ;
      set_removed rq buffer.removed ;
      set_updated rq buffer.updated ;
      set_pending rq buffer.pending ;
    end ;
  Request.register
    ~package ~name:(Package.Derived.reload id).name
    ~descr:(plain "Force full reload for array" @ href)
    ~kind:`GET ~input:(module Junit) ~output:(module Junit)
    (fun () -> reload array) ;
  synchronize array ;
  install signal (update array) add_update_hook ;
  install signal (remove array) add_remove_hook ;
  install signal (fun () -> reload array) add_reload_hook ;
  array

(* -------------------------------------------------------------------------- *)
