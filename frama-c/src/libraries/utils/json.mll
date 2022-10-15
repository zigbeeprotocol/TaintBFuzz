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

(* -------------------------------------------------------------------------- *)
(* --- Json Parser/Lexer                                                  --- *)
(* -------------------------------------------------------------------------- *)

{

type json =
       [ `Assoc of (string * json) list
       | `Bool of bool
       | `Float of float
       | `Int of int
       | `List of json list
       | `Null
       | `String of string ]

type t = json
let equal = (=)
let compare = Stdlib.compare

type token = EOF | TRUE | FALSE | NULL | KEY of char
           | STR of string | INT of string | DEC of string
}

rule token = parse
 '\n' { Lexing.new_line lexbuf ; token lexbuf }
| [ ' ' '\t' '\r' ] { token lexbuf }
| '"' { let buffer = Buffer.create 80 in
        string buffer lexbuf ;
        STR(Buffer.contents buffer) }
| '-'? [ '0'-'9' ]+ { INT(Lexing.lexeme lexbuf) }
| '-'? [ '0'-'9' ]* '.' ['0'-'9']* ( ['e' 'E'] ['-' '+']? ['0'-'9']+ )?
    { DEC(Lexing.lexeme lexbuf) }
| [ '[' ']' '{' '}' ':' ',' ] as c { KEY c }
| "true" { TRUE }
| "false" { FALSE }
| "null" { NULL }
| eof { EOF }
| _ { failwith "un-recognised token" }

and string buffer = parse
  | '"' { () }
  | "\\\\" { Buffer.add_char buffer '\\' ; string buffer lexbuf }
  | "\\n" { Buffer.add_char buffer '\n' ; string buffer lexbuf }
  | "\\t" { Buffer.add_char buffer '\t' ; string buffer lexbuf }
  | "\\r" { Buffer.add_char buffer '\r' ; string buffer lexbuf }
  | "\\\"" { Buffer.add_char buffer '"' ; string buffer lexbuf }
  | '\n' | eof { failwith "non-terminated string" }
  | _ as c { Buffer.add_char buffer c ; string buffer lexbuf }


{

type input = {
  lexbuf : Lexing.lexbuf ;
  mutable token : token ;
}

let skip input =
  if input.token <> EOF then input.token <- token input.lexbuf

(* Termination hints:
   - unless EOF, parse_value always eat a token
   - parse_array always eat a token or call parse_value with non-EOF input
   - parse_object always eat a token
   - parse_entry always eat a token or call parse_value with non-EOF input
*)
let rec parse_value input =
  match input.token with
  | EOF -> `Null
  | TRUE -> skip input ; `Bool true
  | FALSE -> skip input ; `Bool false
  | NULL -> skip input ; `Null
  | STR a -> skip input ; `String a
  | INT a -> skip input ; (try `Int(int_of_string a) with _ -> `String a)
  | DEC a -> skip input ; (try `Float(float_of_string a) with _ -> `String a)
  | KEY '[' -> skip input ; `List (parse_array [] input)
  | KEY '{' -> skip input ; `Assoc (parse_object [] input)
  | _ -> failwith "unexpected token"

and parse_array es input =
  match input.token with
  | EOF -> failwith "non-terminated array"
  | KEY ']' -> skip input ; List.rev es
  | KEY ',' -> skip input ; parse_array es input
  | _ -> let e = parse_value input in parse_array (e::es) input

and parse_object es input =
  match input.token with
  | EOF -> failwith "non-terminated record"
  | KEY '}' -> skip input ; List.rev es
  | KEY ',' -> skip input ; parse_object es input
  | STR a -> skip input ; let e = parse_entry a input in parse_object (e::es) input
  | _ -> failwith "missing name"

and parse_entry a input =
  match input.token with
  | EOF -> failwith "non-terminated record"
  | KEY ':' -> skip input ; parse_entry a input
  | _ -> a , parse_value input

let parse_file input =
  let content = parse_value input in
  if input.token <> EOF then failwith "unexpected end-of-file" ;
  content

exception Error of Filepath.Normalized.t * int * string

let error lexbuf msg =
  let open Lexing in
  let position = Lexing.lexeme_start_p lexbuf in
  let token = Lexing.lexeme lexbuf in
  let path = Filepath.Normalized.of_string position.pos_fname in
  Error(path,position.pos_lnum,
        Printf.sprintf "%s (at %S)" msg token)

let load_lexbuf lexbuf =
  try
    let token = token lexbuf in
    parse_file { lexbuf ; token }
  with Failure msg -> raise (error lexbuf msg)

let load_string text = load_lexbuf (Lexing.from_string text)
let load_channel ?file inc =
  let lexbuf = Lexing.from_channel inc in
  begin
    match file with
    | None -> ()
    | Some pos_fname ->
      let open Lexing in
      lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname }
  end ;
  load_lexbuf lexbuf

let load_file file =
  let inc = open_in file in
  try
    let content = load_channel ~file inc in
    close_in inc ; content
  with e ->
    close_in inc ; raise e

let rec pp fmt v = let open Format in
  match v with
  | `Null -> pp_print_string fmt "null"
  | `Bool b -> pp_print_bool fmt b
  | `String s -> fprintf fmt "%S" s
  | `Int a -> pp_print_int fmt a
  | `Float f -> pp_print_float fmt f
  | `List [] -> pp_print_string fmt "[]"
  | `List (e::es) ->
      Format.fprintf fmt "@[<hov 2>[ %a" pp e ;
      List.iter (fun e -> Format.fprintf fmt ",@ %a" pp e) es ;
      Format.fprintf fmt " ]@]"
  | `Assoc [] -> pp_print_string fmt "{}"
  | `Assoc (e::es) ->
      Format.fprintf fmt "@[<hov 2>{ %a" pp_entry e ;
      List.iter (fun e -> Format.fprintf fmt ",@ %a" pp_entry e) es ;
      Format.fprintf fmt " }@]"

and pp_entry fmt (a,v) = Format.fprintf fmt "@[<hov 2>%S: %a@]" a pp v

let dump_string f s =
  let quote = "\"" in
  f quote ; f (String.escaped s) ; f quote

let rec dump f = function
  | `Null -> f "null"
  | `Bool true -> f "true"
  | `Bool false -> f "false"
  | `String s -> dump_string f s
  | `Int a -> f (string_of_int a)
  | `Float x -> f (string_of_float x)
  | `List [] -> f "[]"
  | `List (e::es) ->
      f "[" ; dump f e ;
      List.iter (fun e -> f "," ; dump f e) es ;
      f "]"
  | `Assoc [] -> f "{}"
  | `Assoc (e::es) ->
      f "{" ;
      dump_entry f e ;
      List.iter (fun e -> f "," ; dump_entry f e) es ;
      f "}"

and dump_entry f (a,v) =
  dump_string f a ; f ":" ; dump f v

let pp_dump fmt v =
  dump (Format.pp_print_string fmt) v

let save_buffer ?(pretty=true) buffer v =
  if pretty then
    Format.fprintf (Format.formatter_of_buffer buffer) "@[%a@]@." pp v
  else
    (dump (Buffer.add_string buffer) v ; Buffer.add_char buffer '\n' )

let save_string ?(pretty=true) v =
  let buffer = Buffer.create 80 in
  save_buffer ~pretty buffer v ;
  Buffer.contents buffer

let save_channel ?(pretty=true) out v =
  if pretty then
    Format.fprintf (Format.formatter_of_out_channel out) "@[%a@]@." pp v
  else
    (dump (output_string out) v ; output_char out '\n' ; flush out)

let save_formatter ?(pretty=true) fmt v =
  if pretty then pp fmt v else pp_dump fmt v

let save_file ?(pretty=true) file v =
  let out = open_out file in
  try
    save_channel ~pretty out v ;
    close_out out
  with e ->
    close_out out ; raise e

let invalid name = raise (Invalid_argument ("Json." ^ name))

let bool = function
  | `Bool b -> b
  | _ -> invalid "bool"

let int = function
  | `Null -> 0
  | `Int n -> n
  | `Float f -> (try int_of_float f with _ -> invalid "int")
  | _ -> invalid "int"

let float = function
  | `Null -> 0.0
  | `Float f -> f
  | `Int n -> (try float_of_int n with _ -> invalid "float")
  | _ -> invalid "float"

let string = function
  | `Null -> ""
  | `Int n -> string_of_int n
  | `Float f -> string_of_float f
  | `String s -> s
  | _ -> invalid "string"

let list = function
  | `Null -> []
  | `List es -> es
  | _ -> invalid "list"

let array = function
  | `Null -> [| |]
  | `List es -> Array.of_list es
  | _ -> invalid "array"

let assoc = function
  | `Null -> []
  | `Assoc fs -> fs
  | _ -> invalid "assoc"

let field f = function
  | `Null -> raise Not_found
  | `Assoc fs -> List.assoc f fs
  | _ -> invalid "field"

let fold f v w = match v with
  | `Null -> w
  | `Assoc fs -> List.fold_left (fun w (e,v) -> f e v w) w fs
  | _ -> invalid "fold"

let of_bool b = `Bool b
let of_int k = `Int k
let of_string s = `String s
let of_float f = `Float f
let of_list xs = `List xs
let of_array xs = `List (Array.to_list xs)
let of_fields m = `Assoc m


(* JSON file cache and merging *)

exception CannotMerge of string

(* Table of filepaths to JSON arrays, to be written at the end of a run *)
let json_tbl = Hashtbl.create 3

let rec merge_assoc_lists la lb =
  let cmp = fun (k1, _) (k2, _) -> String.compare k1 k2 in
  let rec aux acc l1 l2 =
    match l1, l2 with
    | [], [] -> acc
    | [], l | l, [] -> List.rev_append l acc
    | e1 :: r1, e2 :: r2 ->
      let c = cmp e1 e2 in
      if c < 0 then aux (e1 :: acc) r1 l2
      else if c > 0 then aux (e2 :: acc) l1 r2
      else (* c = 0 *)
        let (k1, v1) = e1 in
        let (_, v2) = e2 in
        match v1, v2 with
        | `Assoc a1, `Assoc a2 ->
          let v = `Assoc (merge_assoc_lists a1 a2) in
          aux ((k1, v) :: acc) r1 r2
        | `List l1, `List l2 ->
          let v = `List (l1 @ l2) in
          aux ((k1, v) :: acc) r1 r2
        | o1, o2 ->
          let pp = Yojson.Basic.pretty_to_string in
          raise (CannotMerge
                   ("cannot merge heterogeneous objects '"
                    ^ pp o1 ^ "' and '" ^ pp o2 ^ "'"))
  in
  let r = aux [] (List.sort cmp la) (List.sort cmp lb) in
  List.rev r

let merge_object path json_root_obj =
  let open Yojson.Basic.Util in
  let existing_root_obj =
    try
      match Hashtbl.find json_tbl path with
      | `Assoc _ as root -> root
      | _ -> raise (CannotMerge "JSON root element should be an object")
    with Not_found ->
      `Assoc []
  in
  let existing_assoc = existing_root_obj |> to_assoc in
  let new_assoc = json_root_obj |> to_assoc in
  let merged = merge_assoc_lists existing_assoc new_assoc in
  let merged_obj = `Assoc merged in
  Hashtbl.replace json_tbl path merged_obj

let merge_array path json_root_array =
  let open Yojson.Basic.Util in
  let existing_root_array =
    try
      match Hashtbl.find json_tbl path with
      | `List _ as root -> root
      | _ -> raise (CannotMerge "JSON root element should be an array")
    with Not_found ->
      `List []
  in
  let existing_list = existing_root_array |> to_list in
  let new_list = json_root_array |> to_list in
  let merged_list = `List (existing_list @ new_list) in
  Hashtbl.replace json_tbl path merged_list

let flush_cache () =
  let written =
    Hashtbl.fold (fun (path : Filepath.Normalized.t) json acc ->
        let oc = open_out (path:>string) in
        Yojson.Basic.pretty_to_channel oc json;
        output_char oc '\n'; (* ensure JSON file terminates with a newline *)
        path :: acc
      ) json_tbl []
  in
  Hashtbl.clear json_tbl;
  List.rev written

let json_cache = Hashtbl.create 3

let from_file (path : Filepath.Normalized.t) =
  try
    Hashtbl.find json_cache path
  with Not_found ->
    let json = Yojson.Basic.from_file (path:>string) in
    Hashtbl.replace json_cache path json;
    json

}
