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

type json = Yojson.Basic.t

type buffer = {
  text : Buffer.t ;
  mutable rjson : json list ; (* Current op-codes in reverse order *)
  mutable stack : ( string * json list ) list ;
  mutable fmt : Format.formatter ;
}

let append buffer s k n =
  Buffer.add_substring buffer.text s k n

let flush buffer () =
  let t = buffer.text in
  let n = Buffer.length t in
  if n > 0 then
    let js = `String (Buffer.contents t) in
    buffer.rjson <- js :: buffer.rjson ;
    Buffer.clear t

let push_tag buffer stag =
  let tag = Extlib.format_string_of_stag stag in
  flush buffer () ;
  buffer.stack <- ( tag , buffer.rjson ) :: buffer.stack ;
  buffer.rjson <- []

let pop_tag buffer _tag =
  match buffer.stack with
  | [] -> ()
  | (tag,rjson)::stack ->
    flush buffer () ;
    buffer.stack <- stack ;
    let content = List.rev buffer.rjson in
    buffer.rjson <-
      if content = [] then rjson
      else
        let block = `List ( `String tag :: content ) in
        block :: rjson

let no_mark _tag = ()
let mark_open_tag buffer tg = push_tag buffer tg ; ""
let mark_close_tag buffer tg = pop_tag buffer tg ; ""

let create ?indent ?margin () =
  let buffer = {
    fmt = Format.err_formatter ;
    text = Buffer.create 80 ; rjson = [] ; stack = []
  } in
  let fmt = Format.make_formatter (append buffer) (flush buffer) in
  buffer.fmt <- fmt ;
  begin match indent , margin with
    | None , None -> ()
    | Some k , None ->
      let m = Format.pp_get_margin fmt () in
      Format.pp_set_max_indent fmt (max 0 (min k m))
    | None , Some m ->
      Format.pp_set_margin fmt (max 0 m) ;
      let k = Format.pp_get_max_indent fmt () in
      if k < m-10 then Format.pp_set_max_indent fmt (max 0 (m-10))
    | Some k , Some m ->
      Format.pp_set_margin fmt (max 0 m) ;
      Format.pp_set_max_indent fmt (max 0 (min k (m-10)))
  end ;
  begin
    let open Format in
    pp_set_formatter_stag_functions fmt {
      print_open_stag = no_mark ;
      print_close_stag = no_mark ;
      mark_open_stag = mark_open_tag buffer ;
      mark_close_stag = mark_close_tag buffer ;
    } ;
    Format.pp_set_print_tags fmt false ;
    Format.pp_set_mark_tags fmt true ;
  end ;
  buffer

let bprintf buffer msg = Format.fprintf buffer.fmt msg
let formatter buffer = buffer.fmt

let contents buffer : json =
  Format.pp_print_flush buffer.fmt () ;
  flush buffer () ;
  while buffer.stack <> [] do
    pop_tag buffer ""
  done ;
  match List.rev buffer.rjson with
  | [] -> `Null
  | [`String _ as text] -> text
  | content -> `List ( `String "" :: content )

let format ?indent ?margin msg =
  let buffer = create ?indent ?margin () in
  Format.kfprintf
    (fun _fmt -> contents buffer)
    buffer.fmt msg

let to_json ?indent ?margin pp a =
  let buffer = create ?indent ?margin () in
  pp buffer.fmt a ;
  contents buffer

let rec is_empty (js : json) = match js with
  | `Null -> true
  | `List js -> List.for_all is_empty js
  | `String "" -> true
  | _ -> false

let rec fprintf fmt = function
  | `Null -> ()
  | `String text -> Format.pp_print_string fmt text
  | `List ( `String tag :: content ) ->
    if tag <> "" then
      begin
        Format.fprintf fmt "@{<%s>" tag ;
        List.iter (fprintf fmt) content ;
        Format.fprintf fmt "@}" ;
      end
    else
      List.iter (fprintf fmt) content
  | js -> raise (Yojson.Basic.Util.Type_error("Invalid rich-text format",js))

(* -------------------------------------------------------------------------- *)
