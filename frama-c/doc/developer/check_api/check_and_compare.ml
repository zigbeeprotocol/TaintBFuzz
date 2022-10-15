(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2021                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*  Contact CEA LIST for licensing.                                       *)
(*                                                                        *)
(**************************************************************************)

let replace_space_by_dot s = Str.global_replace (Str.regexp " ") "." s

let repair_word s = 
  let rec repair_word_aux st = 
    try let d1 = String.index st '$'
	in 
	try let d2 = String.index_from st d1 '$'
	    in (Str.string_before st d1)^
	    (repair_word_aux (Str.string_after st (d2+1)))
	with Not_found -> st
    with Not_found -> st
  in
  Str.global_replace (Str.regexp "\\") "" (repair_word_aux s)
 

(** [fill_tbl] takes a file containing data which is 
    as "element_name/type/comment/" or "element_name".
    It fills the hashtable [tbl]
    with all the element [type;comment] or [] recorded 
    with the key "element_name". *)
let fill_tbl tbl file_name =
  try
    let c = open_in file_name in
    try 
      while true do 
	let s = input_line c
	in 
	if not (Str.string_match (Str.regexp "Command.Line") s 0)
	  && not ( Hashtbl.mem tbl s)
	then match (Str.split (Str.regexp "/") s) with
	  | []    -> ()
	  | h::[] -> Hashtbl.add tbl h [] 
	  | h::q  -> Hashtbl.add tbl h q 
      done
    with End_of_file -> close_in c
  with Sys_error _ as exn ->
    Format.eprintf "cannot handle file %s: %s" file_name 
      (Printexc.to_string exn)

(** [fill_list] takes a file containing data which is 
    as "element_name/type/comment/" if (has_type=true) or
    "element_name" if (has_type=false). It fills the list [li]
    with all the element names and alphabetically sorts them. *)
let fill_list li name ~has_type = 
  let fill_list_no_sorting l file_name =
    try let c = open_in file_name in
	try 
	  while true do 
	    let s = input_line c in 
	    if not (Str.string_match
		      (Str.regexp "Command.Line") s 0)&& not ( List.mem s !l) 
	    then begin
	      if has_type then
		try let t =(Str.string_before s
			      (String.index_from s 0 '/' )) in
		    match t with
		    |""  -> ()
		    | _  -> if not( List.mem t !l) 
		      then l := t::!l
		with Not_found ->()
		      else l := s::!l
	    end 
	  done
	with End_of_file -> close_in c
    with Sys_error _ as exn ->
      Format.eprintf "cannot handle file %s: %s" file_name 
	(Printexc.to_string exn) in
  fill_list_no_sorting li name ; 
  li := List.sort String.compare !li

(** [run_oracle] takes two hashtables [t1] and [t2] when called.
    It first tests if the file "run.oracle" is already existing.
    If this file exists, it uses the function [w_tbl] and creates
    [tbl] a hashtable that contains the information found in "run.oracle".
    It first looks for all the elements in common in [t1] and [t2] and then 
    compares the corresponding pieces of information of [t1] and [tbl]
    If the pieces of information are different, it writes this difference.
    It eventually overwrites the "run.oracle" file with
    the pieces of information of the common elements of [t1] and [t2]. 
    If the file "run.oracle" does not exit, it only fills this file with 
    the pieces of information in common using the function [wo_tbl]. *)
let run_oracle t1 t2 =
  let to_fill = ref "" 
  in
  let fill_oracle s =
    try let chan_out = open_out "run.oracle"
	in
	output_string chan_out s;
	close_out chan_out
    with Sys_error _ as exn ->
      Format.eprintf "cannot handle file %s: %s" "run.oracle" 
	(Printexc.to_string exn) 
  in
  let rec string_of_list l = match l with
    | []    -> ""
    | h::[] -> h ^"/"
    | h::q  -> h ^"/"^ (string_of_list q)
  in
  let rec string_of_info_list l = match l with
    | [] -> ""
    | h::[] -> h
    | h::q  ->
      if not (h="")
      then h ^ "\n" ^ (string_of_info_list q)
      else (string_of_info_list q)
  in
  let wo_tbl t k d = 
    try let element_info = Hashtbl.find t k
	in
	to_fill := 
	  !to_fill ^ "\n" ^ k ^ "/" ^ (string_of_list element_info)
    with Not_found -> ()
  in
  let w_tbl t k d = 
    let tbl: (string,string list) Hashtbl.t = Hashtbl.create 197
    in
    fill_tbl tbl "run.oracle";
    try 
      let element_info = Hashtbl.find t k
      in
      to_fill := 
	!to_fill ^ "\n" ^ k ^ "/"^ string_of_list element_info;
      let previous_element_info = Hashtbl.find tbl k 
      in
      if not (element_info = previous_element_info) then
	Format.printf " \n \n ----%s---- \n\n ** Information \
 previously registered in 'run.oracle' :\n %s \n\n ** Information in \
 the current API :\n %s \n "
	  k (string_of_info_list previous_element_info)
	  (string_of_info_list element_info)
    with Not_found -> 
      (* element not previously registered *)
      ()
  in
  Format.printf "%s" " \n \n*****************************\
*************************************\
\nELEMENTS OF THE INDEX OF THE DEVELOPER GUIDE EXISTING \
IN THE CODE: \n*****************************************\
*************************\n\n";
  if (Sys.file_exists "run.oracle") 
  then (Hashtbl.iter (w_tbl t2) t1; 
	fill_oracle !to_fill)
  else (Hashtbl.iter (wo_tbl t2) t1 ;
	fill_oracle !to_fill)
    
    
(** [compare] takes two lists and returns the elements 
    of the first list not in the second list and then the elements
    of the second list not in the first list.
    The two names are corresponding (same order) to the two tables
    and are used in the introduction sentences. *)    
let compare t1 t2 name1 name2 =
  let compare_aux t k =
    if not(List.mem k t) then Format.printf "%s" (k ^ "\n") in
  Format.printf " \n \n*****************************************\
*******************\
\nELEMENTS OF %s NOT IN %s: \n***********************************\
*************************\
\n\n" 
    name1 name2;
  List.iter (compare_aux t2) t1;
  Format.printf " \n \n*******************************************\
*****************\
\nELEMENTS OF %s NOT IN %s: \n************************************\
************************\
\n\n"
    name2 name1; 
  List.iter (compare_aux t1) t2


(** here are used the lexer and parser "check_index_lexer" and
    "check_index_grammar" to create the file "index_file". 
    The files "main.idx" and "code_file" must already exist. *)
let () =
  let index_hstbl: (string,string list) Hashtbl.t = Hashtbl.create 197 in
  let code_hstbl: (string,string list) Hashtbl.t = Hashtbl.create 197 in
  let index_list = ref [] in
  let code_list = ref [] in
  try
    let chan_out = open_out ( "index_file") in
    try
      let chan_in = open_in ( "main.idx") in
      let lexbuf = Lexing.from_channel chan_in in
      let temp =
        repair_word (Check_index_grammar.main Check_index_lexer.token lexbuf)
      in
      let lexbuf_2 =Lexing.from_string temp in
      let result =
        Check_index_grammar.main Check_index_lexer.token_2 lexbuf_2
      in
      output_string chan_out (replace_space_by_dot result);
      close_out chan_out ; close_in chan_in;
      fill_tbl code_hstbl "code_file";
      fill_tbl index_hstbl "index_file";
      fill_list code_list "code_file" ~has_type:true;
      fill_list index_list "index_file" ~has_type:false;
      compare !index_list !code_list "THE INDEX \
OF THE DEVELOPER GUIDE" "THE CODE";
      run_oracle index_hstbl code_hstbl ;
    with Sys_error _ as exn ->
      Format.eprintf "cannot handle file %s: %s" "index_file"
	(Printexc.to_string exn)
  with Sys_error _ as exn ->
    Format.eprintf "cannot handle file %s: %s" "main.idx" 
      (Printexc.to_string exn)
