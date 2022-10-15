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

type permission = { read: bool; write: bool; }
type mode = { current: permission; calls: permission; }

type function_mode = Kernel_function.t * mode

module Mode = struct
  let all_permission = { read = true; write = true; }
  let no_permission = { read = false; write = false; }

  let default = { current = all_permission; calls = no_permission; }
  let all = { current = all_permission; calls = all_permission; }
  let none = { current = no_permission; calls = no_permission; }

  include Datatype.Make_with_collections
      (struct
        include Datatype.Serializable_undefined
        type t = mode
        let name = "Domain_mode.Mode"
        let reprs = [ default ]
        let compare = Stdlib.compare
        let equal = Datatype.from_compare
        let hash = Hashtbl.hash
      end)

  let check str =
    String.iter
      (fun c ->
         if Char.lowercase_ascii c <> 'r' && Char.lowercase_ascii c <> 'w'
         then raise (Invalid_argument ("invalid mode " ^ str)))
      str

  let of_string str =
    check str;
    let calls =
      { read = String.contains str 'R';
        write = String.contains str 'W'; }
    and current =
      { read = String.contains str 'r';
        write = String.contains str 'w'; }
    in
    { current; calls; }

  let to_string t =
    let string_if c b = if b then c else "" in
    string_if "r" t.current.read ^ string_if "w" t.current.write ^
    string_if "R" t.calls.read ^ string_if "W" t.calls.write
end

module Function_Mode = struct
  include Datatype.Pair (Kernel_function) (Mode)
  type key = string

  let of_string ~key ~prev:_ str =
    match str with
    | None -> raise (Invalid_argument ("no value bound to " ^ key))
    | Some str ->
      let get_function str =
        try Globals.Functions.find_by_name str
        with Not_found -> raise (Invalid_argument ("no function " ^ str))
      in
      match String.split_on_char '-' str with
      | [ kf; "" ] -> Some (get_function kf, Mode.none)
      | _ ->
        match String.split_on_char '+' str with
        | [ kf ]       -> Some (get_function kf, Mode.default)
        | [ kf; "" ]   -> Some (get_function kf, Mode.all)
        | [ kf; mode ] -> Some (get_function kf, Mode.of_string mode)
        | _ -> raise (Invalid_argument ("invalid argument " ^ str))

  let to_string ~key:_ = function
    | None -> None
    | Some (kf, mode) ->
      Some (Kernel_function.get_name kf ^ "+" ^ Mode.to_string mode)
end

include Datatype.List (Function_Mode)
