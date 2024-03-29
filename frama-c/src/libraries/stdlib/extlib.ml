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

let nop _ = ()

external id: 'a -> 'a = "%identity"

let adapt_filename f =
  let change_suffix ext =
    try Filename.chop_extension f ^ ext
    with Invalid_argument _ -> f ^ ext
  in
  change_suffix (if Dynlink.is_native then ".cmxs" else ".cmo")

(* [max_cpt t1 t2] returns the maximum of [t1] and [t2] wrt the total ordering
   induced by tags creation. This ordering is defined as follows:
   forall tags t1 t2,
   t1 <= t2 iff
   t1 is before t2 in the finite sequence
   [0; 1; ..; max_int; min_int; min_int-1; -1] *)
let max_cpt c1 c2 = max (c1 + min_int) (c2 + min_int) - min_int

let number_to_color n =
  let color = ref 0 in
  let number = ref n in
  for _i = 0 to 7 do
    color := (!color lsl 1) +
             (if !number land 1 <> 0 then 1 else 0) +
             (if !number land 2 <> 0 then 256 else 0) +
             (if !number land 4 <> 0 then 65536 else 0);
    number := !number lsr 3
  done;
  !color

(* ************************************************************************* *)
(** {2 Function builders} *)
(* ************************************************************************* *)

exception Unregistered_function of string

let mk_labeled_fun s =
  raise
    (Unregistered_function
       (Printf.sprintf "Function '%s' not registered yet" s))

let mk_fun s = ref (fun _ -> mk_labeled_fun s)

(* ************************************************************************* *)
(** {2 Function combinators} *)
(* ************************************************************************* *)

let ($) f g x = f (g x)

let swap f x y = f y x

let uncurry f x = f (fst x) (snd x)

let iter_uncurry2 iter f v =
  iter (fun a b -> f (a, b)) v

(* ************************************************************************* *)
(** {2 Tuples} *)
(* ************************************************************************* *)

let nest b (a, c) = (a, b), c

let flatten ((a, b), c) = a, b, c

(* ************************************************************************* *)
(** {2 Lists} *)
(* ************************************************************************* *)

let as_singleton = function
  | [a] -> a
  | _ -> invalid_arg "Extlib.as_singleton"

let rec last = function
  | [] -> invalid_arg "Extlib.last"
  | [a] -> a
  | _ :: l -> last l

let filter_out f ls = List.filter (fun x -> not (f x)) ls

let replace cmp x l =
  let rec aux = function
    | [] -> [x]
    | y::l -> if cmp x y then x::l else y :: aux l
  in aux l

let filter_map filter f l =
  let rec aux = function
      [] -> []
    | x::tl -> if filter x then f x :: aux tl else aux tl
  in aux l
let filter_map' f filter l=
  let rec aux = function
    | [] -> []
    | x::tl -> let x' = f x in if filter x' then x' :: aux tl else aux tl
  in aux l
let rec filter_map_opt f = function
  | [] -> []
  | x::tl ->
    match f x with
    | None -> filter_map_opt f tl
    | Some x' -> x' :: filter_map_opt  f tl

let rec fold_map f acc = function
  | [] -> acc, []
  | x::tl ->
    let (acc,x) = f acc x in
    let (acc,tl) = fold_map f acc tl in
    (acc,x::tl)

let rec fold_map_opt f acc = function
  | [] -> acc, []
  | x::tl ->
    match f acc x with
    | acc, None -> fold_map_opt f acc tl
    | acc, Some x ->
      let (acc,tl) = fold_map_opt f acc tl in
      (acc,x::tl)

let product_fold f acc e1 e2 =
  List.fold_left
    (fun acc e1 -> List.fold_left (fun acc e2 -> f acc e1 e2) acc e2)
    acc e1

let product f e1 e2 = product_fold (fun acc e1 e2 -> f e1 e2 ::acc) [] e1 e2

let find_index f l =
  let rec aux i = function
      [] -> raise Not_found
    | x::l -> if f x then i else aux (i+1) l
  in aux 0 l

let rec list_compare cmp_elt l1 l2 =
  if l1 == l2 then 0
  else
    match l1, l2 with
    | [], [] -> assert false (* included in l1 == l2 above *)
    | [], _ :: _ -> -1
    | _ :: _, [] -> 1
    | v1::r1, v2::r2 ->
      let c = cmp_elt v1 v2 in
      if c = 0 then list_compare cmp_elt r1 r2 else c

let opt_of_list =
  function
  | [] -> None
  | [a] -> Some a
  | _ -> raise (Invalid_argument "Extlib.opt_of_list")

let iteri f l = let i = ref 0 in List.iter (fun x -> f !i x; incr i) l

let mapi f l =
  let res =
    snd (List.fold_left (fun (i,acc) x -> (i+1,f i x :: acc)) (0,[]) l)
  in List.rev res

let subsets k l =
  let rec aux k l len =
    if k = 0 then [[]]
    else if len < k then []
    else if len = k then [l]
    else
      match l with
      | h :: t ->
        let l1 = List.map (fun sl -> h :: sl) (aux (k-1) t (len-1)) in
        let l2 = aux k t (len-1)
        in l1 @ l2
      | [] -> assert false
  in aux k l (List.length l)


let list_first_n n l =
  let rec aux acc n = function
    | h :: t when n > 0 -> aux (h :: acc) (n-1) t
    | _ -> acc
  in
  List.rev (aux [] n l)

let rec list_remove_first_n n = function
  | _h :: t when n > 0 -> list_remove_first_n (n-1) t
  | l -> l

let list_slice ?(first = 0) ?last l =
  let len = lazy (List.length l) in
  let normalize i =
    (* normalize negative values *)
    if i >= 0
    then i
    else
      let n = Lazy.force len in
      if i + n >= 0 then i + n else 0
  in
  (* Remove first elements *)
  let first = normalize first in
  let l = list_remove_first_n first l in
  (* Remove last elements *)
  match last with
  | None -> l
  | Some n -> list_first_n (normalize n - first) l

(* ************************************************************************* *)
(** {2 Options} *)
(* ************************************************************************* *)

let opt_fold f o b =
  match o with
  | None -> b
  | Some a -> f a b

let merge_opt f k o1 o2 =
  match o1,o2 with
  | None, None -> None
  | Some x, None | None, Some x -> Some x
  | Some x1, Some x2 -> Some (f k x1 x2)

let opt_filter f = function
  | None -> None
  | (Some x) as o -> if f x then o else None

let the ~exn = function
  | None -> raise exn
  | Some x -> x

let opt_hash hash v = match v with
  | None -> 31179
  | Some v -> hash v

let opt_map2 f x y = match x, y with
  | None, _ | _, None -> None
  | Some x, Some y -> Some (f x y)

(* ************************************************************************* *)
(** Booleans                                                                 *)
(* ************************************************************************* *)

let xor x y = if x then not y else y

(* ************************************************************************* *)
(** {2 Performance} *)
(* ************************************************************************* *)

external address_of_value: 'a -> int = "address_of_value" [@@noalloc]

(* ************************************************************************* *)
(** {2 Exception catcher} *)
(* ************************************************************************* *)

let try_finally ~finally f x =
  let r = try f x with e -> finally () ; raise e in
  finally () ; r

(* ************************************************************************* *)
(** System commands *)
(* ************************************************************************* *)

(*[LC] due to Unix.exec calls, at_exit might be cloned into child process
  and executed when they are canceled early.

  The alternative, such as registering an daemon that raises an exception,
  hence interrupting the process, might not work: child processes still need to
  run some daemons, such as [flush_all] which is registered by default. *)

let rec mkdir ?(parents=false) name perm =
  try Unix.mkdir name perm
  with
  | Unix.Unix_error (Unix.ENOENT,_,_) when parents ->
    let parent_name = Filename.dirname name in
    if name <> parent_name then
      begin
        mkdir ~parents parent_name perm;
        Unix.mkdir name perm
      end
  | e -> raise e

let pid = Unix.getpid ()
let safe_at_exit f =
  at_exit
    begin fun () ->
      let child = Unix.getpid () in
      if child = pid then f ()
    end

let safe_remove f = try Unix.unlink f with Unix.Unix_error _ -> ()

let rec safe_remove_dir d =
  try
    Array.iter
      (fun a ->
         let f = Printf.sprintf "%s/%s" d a in
         if Sys.is_directory f then safe_remove_dir f else safe_remove f
      ) (Sys.readdir d) ;
    Unix.rmdir d
  with Unix.Unix_error _ | Sys_error _ -> ()

let cleanup_at_exit f = safe_at_exit (fun () -> safe_remove f)

exception Temp_file_error of string

let temp_file_cleanup_at_exit ?(debug=false) s1 s2 =
  let file, out =
    try Filename.open_temp_file s1 s2
    with Sys_error s -> raise (Temp_file_error s)
  in
  (try close_out out with Unix.Unix_error _ -> ());
  safe_at_exit
    begin fun () ->
      if debug then
        begin
          if Sys.file_exists file then
            Format.printf
              "[extlib] Debug: not removing file %s@." file;
        end
      else
        safe_remove file
    end ;
  file

let temp_dir_cleanup_at_exit ?(debug=false) base =
  let rec try_dir_cleanup_at_exit limit base =
    let file = Filename.temp_file base ".tmp" in
    let dir = Filename.chop_extension file ^ ".dir" in
    safe_remove file;
    try
      Unix.mkdir dir 0o700 ;
      safe_at_exit
        begin fun () ->
          if debug then
            begin
              if Sys.file_exists dir then
                Format.printf
                  "[extlib] Debug: not removing dir %s@." dir;
            end
          else
            safe_remove_dir dir
        end ;
      dir
    with Unix.Unix_error(err,_,_) ->
      if limit < 0 then
        raise (Temp_file_error (Unix.error_message err))
      else
        try_dir_cleanup_at_exit (pred limit) base
  in
  try_dir_cleanup_at_exit 10 base

(* ************************************************************************* *)
(** Strings *)
(* ************************************************************************* *)

let compare_strings s1 s2 len =
  try
    for i = 0 to len - 1 do if s1.[i] <> s2.[i] then raise Exit; done;
    true
  with Exit -> false
     | Invalid_argument _ -> raise (Invalid_argument "Extlib.compare_strings")

let string_prefix ?(strict=false) prefix s =
  let add = if strict then 1 else 0 in
  String.length s >= String.length prefix + add
  && compare_strings prefix s (String.length prefix)

let string_del_prefix ?(strict=false) prefix s =
  if string_prefix ~strict prefix s then
    Some
      (String.sub s
         (String.length prefix) (String.length s - String.length prefix))
  else None

let string_suffix ?(strict=false) suffix s =
  let len = String.length s in
  let suf_len = String.length suffix in
  let strict_len = if strict then suf_len + 1 else suf_len in
  len >= strict_len &&
  compare_strings suffix (String.sub s (len - suf_len) suf_len) suf_len

let string_del_suffix ?(strict=false) suffix s =
  if string_suffix ~strict suffix s then
    Some
      (String.sub s 0 (String.length s - String.length suffix))
  else None

let string_split s i =
  let s1 = String.sub s 0 i in
  let s2 = String.sub s (i+1) (String.length s - i -1) in
  (s1,s2)

let make_unique_name mem ?(sep=" ") ?(start=2) from =
  let rec build base id =
    let fullname = base ^ sep ^ string_of_int id in
    if mem fullname then build base (succ id) else id,fullname
  in
  if mem from then build from start else (0,from)

let strip_underscore s =
  let l = String.length s in
  let rec start i =
    if i >= l then l
    else if s.[i] = '_' then start (i + 1) else i
  in
  let st = start 0 in
  if st = l then ""
  else begin
    let rec finish i =
      (* We know that we will stop at >= st >= 0 *)
      if s.[i] = '_' then finish (i - 1) else i
    in
    let fin = finish (l - 1) in
    String.sub s st (fin - st + 1)
  end

let html_escape s =
  let buf = Buffer.create (String.length s) in
  String.iter
    (function
      | '<' -> Buffer.add_string buf "&lt;"
      | '>' -> Buffer.add_string buf "&gt;"
      | '&' -> Buffer.add_string buf "&amp;"
      | c -> Buffer.add_char buf c
    ) s ;
  Buffer.contents buf

let format_string_of_stag = function
  | Format.String_tag tag -> tag
  | _ -> raise (Invalid_argument "unsupported tag extension")

(* ************************************************************************* *)
(** Comparison functions *)
(* ************************************************************************* *)

external compare_basic: 'a -> 'a -> int = "%compare"

let compare_ignore_case s1 s2 =
  String.compare
    (String.lowercase_ascii s1)
    (String.lowercase_ascii s2)

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
