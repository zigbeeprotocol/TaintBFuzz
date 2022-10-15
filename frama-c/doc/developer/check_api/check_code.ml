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

(* do not work with OCaml 4 or higher *)

open Odoc_html
open Odoc_module
open Odoc_info

let remove_nl s = Str.global_replace (Str.regexp "\n") "" s 
let remove_useless_space s = Str.global_replace (Str.regexp "  ") " " s

let doc_dev_path = ref "."

let print_in_file l =
  let rec string_of_list li = match li with
    | []   -> ""
    | h :: q ->  h ^ "\n" ^ string_of_list q
  in
  let file_path = !doc_dev_path ^ "/code_file" in
  try 
    let chan_out = open_out file_path in
    output_string chan_out (string_of_list l) ;
    flush chan_out ;
    close_out chan_out 
  with Sys_error _ as exn ->
    Format.eprintf
      "cannot handle file %s: %s" 
      file_path
      (Printexc.to_string exn)

module Generator (G : Odoc_html.Html_generator) = struct

  class html = object (self)

    inherit G.html as super 
    val mutable last_name = ""
    val mutable last_type = ""
    val mutable last_info = ""
    val mutable to_print = []

    (** Print html code for the given list of raised exceptions.*)
    method html_of_raised_exceptions b l = match l with
    | [] -> ()
    | (s, t) :: [] ->
      self#html_of_text b t;
      let temp =
	last_info ^ " raised exception: " 
	^ Odoc_info.string_of_text [Raw s] ^ "." 
      in
      last_info <- temp
    | _ -> 
      let temp = last_info ^ " raised exceptions: " in
      last_info <- temp;
      List.iter
	(fun (ex, desc) ->
          self#html_of_text b desc;
	  let temp = last_info ^ ", " ^ Odoc_info.string_of_text desc in
	  last_info <- temp)
	l

    method html_of_info ?(cls="") ?(indent=true) b = function
    | None ->
      ()
    | Some info ->
      (match info.Odoc_info.i_deprecated with
      | None -> ()
      | Some d -> 
	self#html_of_text b d;
	last_info <- string_of_text d);
      (match info.Odoc_info.i_desc with
      | None -> ()
      | Some d when d = [Odoc_info.Raw ""] -> ()
      | Some d -> 
	self#html_of_text b d;
	last_info <- string_of_text d);
      self#html_of_raised_exceptions b info.Odoc_info.i_raised_exceptions;
      self#html_of_return_opt b info.Odoc_info.i_return_value;
      self#html_of_custom b info.Odoc_info.i_custom

    (** Print html code for the first sentence of a description.
	The titles and lists in this first sentence has been removed.*)
    method html_of_info_first_sentence b = function
    | None -> ()
    | Some info ->
      match info.Odoc_info.i_desc with
      | None -> ()
      | Some d when d = [Odoc_info.Raw ""] -> ()
      | Some d ->
	self#html_of_text b
          (Odoc_info.text_no_title_no_list
             (Odoc_info.first_sentence_of_text d));
	last_info <- string_of_text
	  (Odoc_info.text_no_title_no_list
             (Odoc_info.first_sentence_of_text d));

    method generate module_list =
      super#generate module_list;
      print_in_file to_print

    method private html_of_type_expr_param_list_1 b m_name t =
      if string_of_type_param_list t <> "" then
	last_type <- 
	  last_type ^ "parameters: "^ string_of_type_param_list t 
	^ ", constructors: " 

    method private html_of_type_expr_list_2 ?par b m_name sep l =
      last_type <- last_type ^ " of " ^ string_of_type_list ?par sep l 

    method private html_of_type_expr_3 b m_name t =
      last_type <- last_type ^ ": " ^ string_of_type_expr t

    method html_of_type_expr b m_name t =
      last_type <- string_of_type_expr t

    method html_of_class_type_param_expr_list b m_name l =
      last_type <- string_of_class_type_param_list l 

    method html_of_class_parameter_list b father c =
      last_type <- string_of_class_params c 

    method html_of_type_expr_param_list b m_name t =
      last_type <- string_of_type_param_list t 

    method html_of_module_type b ?code m_name t =
      last_type <- string_of_module_type ?code t 

    method html_of_module_parameter b father p =
      let s_functor, s_arrow =
	if !Odoc_html.html_short_functors then "", "" else "functor ", "-> "
      in
      last_type <- last_type ^ s_functor ^ "(" ^ p.mp_name ^ " : ";
      self#html_of_module_type_kind b father p.mp_kind;
      last_type <- last_type ^ " ) " ^ s_arrow

    (** Print html code to display the given module type kind. *)
    method html_of_module_type_kind b father ?modu ?mt = function
    | Module_type_struct eles ->
      (match mt with
      | None ->
	(match modu with
	| None ->
	  last_type <- last_type ^ "sig ";
          List.iter (self#html_of_module_element b father) eles;
	  last_type <- last_type ^ " end "
	| Some m ->
	  last_type <- last_type ^ "sig ";
          List.iter (self#html_of_module_element b father) eles;
	  last_type <- last_type ^ " end ")
      | Some mt ->
	last_type <- last_type ^ mt.mt_name)
    | Module_type_functor (p, k) ->
      self#html_of_module_parameter b father p;
      self#html_of_module_type_kind b father ?modu ?mt k
    | Module_type_alias a ->
      last_type <- last_type ^ a.Module.mta_name
    | Module_type_with (k, s) ->
      self#html_of_module_type_kind b father ?modu ?mt k;
      last_type <- last_type ^ s
    | Module_type_typeof s ->
      last_type <- last_type ^ " module type of " ^ s

    method html_of_module_kind b father ?modu = function
    | Module_struct eles ->
      (match modu with
      | None ->
	last_type <- last_type ^ "sig " ;
	List.iter (self#html_of_module_element b father) eles;
	last_type <- last_type ^ "end "
      | Some m ->
	last_type <- last_type ^ "sig " ;
	List.iter (self#html_of_module_element b father) eles;
	last_type <- last_type ^ "end ");
    | Module_alias a ->
      last_type <- last_type ^ (a.Module.ma_name)
    | Module_functor (p, k) ->
      self#html_of_module_parameter b father p;
      (match k with
      | Module_functor _ -> ()
      | _ when !Odoc_html.html_short_functors ->
	last_type <- last_type ^ " : "
      | _ -> ());
      self#html_of_module_kind b father ?modu k;
    | Module_apply (k1, k2) ->
      self#html_of_module_kind b father k1;
      self#html_of_text b [Code "("];
      last_type <- last_type ^ " ( " ;
      self#html_of_module_kind b father k2;
      self#html_of_text b [Code ")"];
      last_type <- last_type ^ " ) " 
    | Module_with (k, s) ->
      self#html_of_module_type_kind b father ?modu k;
      last_type <- last_type ^ s
    | Module_constraint (k, tk) ->
      self#html_of_module_kind b father ?modu k
    | Module_typeof s ->
      last_type <- last_type ^ " module type of " ^ s
    | Module_unpack (code, mta) ->
      (match mta.mta_module with
      | None -> last_type <- last_type ^ self#escape code
      | Some mt -> last_type <- last_type ^ mt.Module.mt_name ^ self#escape code)

    method html_of_value b v =
      last_name <-  v.Value.val_name;
      last_type <- string_of_type_expr v.Value.val_type;
      super#html_of_value b v

    method html_of_exception b e =
      last_name <- e.Exception.ex_name;
      last_type <- 
        (match e.Exception.ex_args with
           | Odoc_type.Cstr_tuple t -> Odoc_info.string_of_type_list " " t
           | Odoc_type.Cstr_record r -> Odoc_info.string_of_record r
        );
      super#html_of_exception b e

    method private print_record b father l =
        last_type <- last_type ^ "{";
        let print_one r =
          if last_type <> "" &&
               String.get last_type ((String.length last_type) -1) = '{'
          then begin
            if r.Type.rf_mutable then last_type <- last_type ^ "mutable "
          end else begin
            if r.Type.rf_mutable then last_type <- last_type ^ "; mutable "
            else last_type <- last_type ^ "; "
          end;
          last_type <- last_type ^ r.Type.rf_name ;
          self#html_of_type_expr_3 b father r.Type.rf_type;
          self#html_of_info b r.Type.rf_text
        in
        print_concat b "\n" print_one l;
        last_type <- last_type ^ "}"

    method html_of_type b t =
      last_name <- t.Type.ty_name;
      last_type <- "";
      Odoc_info.reset_type_names ();
      let father = Name.father t.Type.ty_name in
      self#html_of_type_expr_param_list_1 b father t;
      (match t.Type.ty_kind with
      | Type.Type_abstract -> ()
      | Type.Type_variant l ->
        let print_one constr =
          last_type <- last_type ^ " | " ^ constr.Type.vc_name ;
          (match constr.Type.vc_args with
          | Odoc_type.Cstr_tuple [] -> ()
          | Odoc_type.Cstr_tuple l ->
              self#html_of_type_expr_list_2 ~par: false b father " * " l
          | Odoc_type.Cstr_record r ->
              self#print_record b father r
          );
          self#html_of_info b constr.Type.vc_text
        in
        print_concat b "\n" print_one l;
      | Type.Type_record l -> self#print_record b father l
      | _ -> ());
      self#html_of_info b t.Type.ty_info;

    method html_of_attribute b a =
      last_name <- a.Value.att_value.Value.val_name;
      last_type <- "";
      super#html_of_attribute b a

    method html_of_method b m =
      last_name <- m.Value.met_value.Value.val_name; 
      last_type <- "";
      super#html_of_method b m  

    method html_of_module b ?(info=true) ?(complete=true) ?(with_link=true) m =
      last_name <- m.Module.m_name;
      last_type <- "";
      let father = Name.father m.m_name in
      self#html_of_module_kind b father ~modu: m m.m_kind;
      last_name <- m.Module.m_name;
      if info then
        if complete then self#html_of_info ~indent:false b m.m_info
        else self#html_of_info_first_sentence b m.m_info

    method html_of_modtype b ?(info=true) ?(complete=true) ?(with_link=true) mt =
      last_name <- mt.Module.mt_name;
      last_type <- "" ;
      let father = Name.father mt.mt_name in
      (match mt.mt_kind with
      | None -> ()
      | Some k -> self#html_of_module_type_kind b father ~mt k);
      last_name <- mt.Module.mt_name;
      if info then
        if complete then self#html_of_info ~indent: false b mt.mt_info
        else self#html_of_info_first_sentence b mt.mt_info

    method html_of_included_module b im =
      last_name <- im.Module.im_name;
      last_type <- "" ;
      last_name <- im.Module.im_name;
      self#html_of_info b im.im_info

    method html_of_class b ?(complete=true) ?(with_link=true) c =
      last_name <- c.Class.cl_name;
      last_type <- "" ;
      super#html_of_class b ~complete:complete ~with_link:with_link c

    method html_of_class_type b ?(complete=true) ?(with_link=true) ct =
      last_name <- ct.Class.clt_name;
      last_type <- "" ;
      super#html_of_class_type b ~complete:complete ~with_link:with_link ct 

    method private html_of_plugin_developer_guide _t =
      let temp = 
	last_name ^ "/" 
	^ remove_useless_space
	  (remove_useless_space (remove_nl (last_type ^ "/" ^ last_info ^ "/")))
      in
      to_print <- temp :: to_print;
      last_name <- "" ;
      last_type <- "" ;
      last_info <- "";
      ""

    initializer
      tag_functions <-
	("plugin", self#html_of_plugin_developer_guide) :: tag_functions
  end
end

let () =
  Odoc_args.extend_html_generator (module Generator : Odoc_gen.Html_functor);
  Odoc_args.add_option
    ("-docdevpath",
     Arg.Set_string doc_dev_path,
     "Frama-C documentation directory")
