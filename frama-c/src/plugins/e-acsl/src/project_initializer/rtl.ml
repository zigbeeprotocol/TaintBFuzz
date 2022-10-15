(**************************************************************************)
(*                                                                        *)
(*  This file is part of the Frama-C's E-ACSL plug-in.                    *)
(*                                                                        *)
(*  Copyright (C) 2012-2021                                               *)
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

open Cil_types
open Cil_datatype

let rtl_file () = Options.Share.get_file ~mode:`Must_exist "e_acsl.h"

(* create the RTL AST in a fresh project *)
let create_rtl_ast prj =
  Project.on
    prj
    (fun () ->
       (* compute the RTL AST in the standard E-ACSL setting *)
       Options.setup ~rtl:true ();
       Kernel.Files.set [ rtl_file () ];
       Ast.get ())
    ()

(* Note: vids, sids and eids are shared between projects (see implementation of
   [Cil_const]). Therefore, no need to set them when inserting the corresponding
   global into the AST. *)

(* Tables that contain RTL's symbols. Useful to know whether some symbols is
    part of the RTL. *)
module Symbols: sig
  val add_global: global -> unit
  val mem_global: global -> bool
  val add_kf: kernel_function -> unit
  val mem_kf: kernel_function -> bool
  val add_vi: string -> varinfo -> unit
  val mem_vi: string -> bool
  exception Unregistered of string
  val find_vi: string -> varinfo (* may raise Unregistered *)
  val replacement: get_name:(string -> string) -> varinfo -> varinfo
  val _debug: unit -> unit
end = struct

  let globals: unit Global.Hashtbl.t = Global.Hashtbl.create 17
  let kfs: unit Kernel_function.Hashtbl.t = Kernel_function.Hashtbl.create 17
  let vars
    : varinfo Datatype.String.Hashtbl.t
    = Datatype.String.Hashtbl.create 17

  let add_global g = Global.Hashtbl.add globals g ()
  let mem_global g = Global.Hashtbl.mem globals g

  let add_kf g = Kernel_function.Hashtbl.add kfs g ()
  let mem_kf g = Kernel_function.Hashtbl.mem kfs g

  let add_vi s vi = Datatype.String.Hashtbl.add vars s vi
  let mem_vi s = Datatype.String.Hashtbl.mem vars s
  exception Unregistered of string
  let find_vi s =
    try Datatype.String.Hashtbl.find vars s
    with Not_found -> raise (Unregistered s)

  let replacement ~get_name fvi =
    let name = get_name fvi.vorig_name in
    try
      find_vi name
    with Unregistered _ ->
      Options.fatal
        "Unable to find RTL function '%s' to replace function '%s'"
        name
        fvi.vname

  let _debug () =
    Global.Hashtbl.iter
      (fun g () -> Format.printf "GLOBAL %a@." Printer.pp_global g)
      globals;
    Kernel_function.Hashtbl.iter
      (fun kf () -> Format.printf "KF %a@." Kernel_function.pretty kf)
      kfs;
    Datatype.String.Hashtbl.iter
      (fun s vi -> Format.printf "VAR %s -> %a@." s Printer.pp_varinfo vi)
      vars

end

(* Internal module to store the associations between symbols in the RTL project
   and their corresponding symbols in the user's project. *)
module Assocs: sig
  val clear: unit -> unit
  (** Clear stored associations. *)

  val add_kf: global -> kernel_function -> unit
  (** Add an association between a global in the RTL project and the
      corresponding kernel function in the user's project. *)

  val mem_kf: global -> bool
  (** Returns true if the given global from the RTL project has a corresponding
      kernel function in the user's project. *)

  val get_kf: global -> kernel_function
  (** Returns the corresponding kernel function from the user's project for the
      given global in the RTL project. *)

  val add_vi: varinfo -> varinfo -> unit
  (** [add_vi rtl_vi user_vi] adds an association between a [varinfo] in the
      RTL project and the corresponding [varinfo] in the user's project. *)

  val find_vi: varinfo -> varinfo
  (** [find_vi rtl_vi] returns the corresponding [varinfo] from the user's
      project for the given [varinfo] in the RTL project if it exists, or raise
      [Not_found] otherwise. *)

  val add_li: logic_info -> logic_info -> unit
  (** [add_li rtl_li user_li] adds an association between a [logic_info] in the
      RTL project and the corresponding [logic_info] in the user's project. *)

  val find_li: logic_info -> logic_info
  (** [find_li rtl_li] returns the corresponding [logic_info] from the user's
      project for the given [logic_info] in the RTL project if it exists,
      or raise [Not_found] otherwise. *)

end = struct
  let kfs: kernel_function Global.Hashtbl.t = Global.Hashtbl.create 17
  let vars: varinfo Varinfo.Hashtbl.t = Varinfo.Hashtbl.create 17
  let logic_vars: logic_info Logic_info.Hashtbl.t = Logic_info.Hashtbl.create 17

  let clear () =
    Global.Hashtbl.clear kfs;
    Varinfo.Hashtbl.clear vars;
    Logic_info.Hashtbl.clear logic_vars

  let add_kf rtl_g user_kf = Global.Hashtbl.replace kfs rtl_g user_kf
  let mem_kf rtl_g = Global.Hashtbl.mem kfs rtl_g
  let get_kf rtl_g =
    try
      Global.Hashtbl.find kfs rtl_g
    with Not_found ->
      Options.fatal
        "Unable to find user kf corresponding to %a. Assocs.mem_kf should be \
         used before calling Assocs.get_kf"
        Printer.pp_global rtl_g

  let add_vi rtl_vi user_vi = Varinfo.Hashtbl.replace vars rtl_vi user_vi
  let find_vi rtl_vi = Varinfo.Hashtbl.find vars rtl_vi

  let add_li rtl_li user_li = Logic_info.Hashtbl.replace logic_vars rtl_li user_li
  let find_li rtl_li = Logic_info.Hashtbl.find logic_vars rtl_li
end


(* NOTE: do not use [Mergecil.merge] since all [ast]'s symbols must be kept
   unchanged: so do it ourselves. Thanksfully, we merge in a particular
   setting because we know what the RTL is. Therefore merging is far from being
   as complicated as [Mergecil]. *)

(* lookup globals from [rtl_ast] in the current [ast] and fill the [Symbols]'
   tables.
   @return the list of globals to be inserted into [ast], in reverse order. *)
let lookup_rtl_globals rtl_ast =
  (* [do_it ~add ~assoc mem acc l g] checks whether the global does exist in the
     user's AST. If not, add it to the corresponding symbol table(s). If yes,
     save the association between the global in the user's AST and the global in
     the RTL. *)
  let rec do_it ?(add=fun _g -> ()) ?(assoc=fun _g -> ()) mem acc l g =
    if mem g then begin
      assoc g;
      do_globals (g :: acc) l
    end else begin
      add g;
      Symbols.add_global g;
      do_globals (g :: acc) l
    end
  (* [do_ty] is [do_it] for types *)
  and do_ty acc l g kind tname =
    do_it (fun _ -> Globals.Types.mem_type kind tname) acc l g
  and do_globals acc globs =
    match globs with
    | [] ->
      acc
    | GType(ti, _loc) as g :: l ->
      do_ty acc l g Logic_typing.Typedef ti.tname
    | GCompTag(ci, _loc) | GCompTagDecl(ci, _loc) as g :: l ->
      let k = if ci.cstruct then Logic_typing.Struct else Logic_typing.Union in
      do_ty acc l g k ci.cname
    | GEnumTag(ei, _loc) | GEnumTagDecl(ei, _loc) as g :: l  ->
      do_ty acc l g Logic_typing.Enum ei.ename
    | GVarDecl(vi, (pos, _)) | GVar(vi, _, (pos, _)) as g :: l  ->
      let tunit = Translation_unit pos.Filepath.pos_path in
      let get_old_vi_opt vi =
        Globals.Syntactic_search.find_in_scope vi.vorig_name tunit
      in
      let mem _g =
        let g = get_old_vi_opt vi in
        Option.is_some g
      in
      let add g =
        Symbols.add_vi vi.vname vi;
        match g with
        | GVarDecl _ -> Globals.Vars.add_decl vi
        | GVar(_, ii, _) -> Globals.Vars.add vi ii
        | _ -> assert false
      in
      let assoc _g =
        (* [assoc] is called if [mem] returns true, so the option returned by
           [get_old_vi_opt] is [Some] by construction. *)
        let old_vi = get_old_vi_opt vi in
        Assocs.add_vi vi (Option.get old_vi)
      in
      do_it ~add ~assoc mem acc l g
    | GFunDecl(_, vi, _loc) | GFun({ svar = vi }, _loc) as g :: l ->
      let add _g =
        Symbols.add_vi vi.vname vi;
        (* functions will be registered in kernel's table after substitution of
           RTL's symbols inside them *)
      in
      let assoc g =
        let kf = Globals.Functions.find_by_name vi.vname in
        Assocs.add_kf g kf
      in
      do_it ~add ~assoc (fun _ -> Globals.Functions.mem_name vi.vname) acc l g
    | GAnnot (Daxiomatic (name, galist, _, _) as ga, _) as g :: l ->
      (* processing axiomatics *)
      let fun_or_preds =
        (* extract the functions and predicates from the axiomatic *)
        List.filter_map
          (fun ga ->
             match ga with
             | Dfun_or_pred (li, _) -> Some li
             | _ -> None)
          galist
      in
      let mem _ =
        (* check if some function or predicate of the axiomatic [exists] in the
           user's project, if all the functions and predicates are in the user's
           project ([forall]), and store which function and predicate are in the
           user's project in [conflicting_lis]. *)
        let exists, forall, conflicting_lis =
          List.fold_left
            (fun (exists, forall, conflicting_lis) li ->
               let lv_name = li.l_var_info.lv_name in
               let li_exists = Logic_env.Logic_info.mem lv_name in
               let conflicting_lis =
                 if li_exists then li :: conflicting_lis else conflicting_lis
               in
               exists || li_exists, forall && li_exists, conflicting_lis)
            (false, true, [])
            fun_or_preds
        in
        (* The axiomatic is considered "in the user's project" if and only if
           all its functions and predicates are in the user's project. If only
           some of them are in it then it is an error, and if none of them are
           then the axiomatic is not in the user's project. *)
        let in_user_prj =
          if exists && not forall then
            Options.abort
              "@[The following logic functions or predicates@ \
               are in conflict with logic functions or predicates from the@ \
               axiomatic '%s' in the E-ACSL runtime library, please rename@ \
               them:@ %a@]"
              name
              (Pretty_utils.pp_list
                 ~sep:",@ "
                 Printer.pp_logic_info)
              conflicting_lis
          else
            forall
        in
        (* If the axiomatic is not "in the user's project", check if a different
           axiomatic with the same name is in it. *)
        if not in_user_prj then begin
          let ip_from_ga = Property.ip_of_global_annotation ga in
          let found =
            try
              Property_status.iter
                (fun ppt ->
                   if List.exists (Property.equal ppt) ip_from_ga
                   then raise Exit);
              false
            with Exit ->
              true
          in
          if found then
            Options.abort
              "@[The axiomatic '%s' is in conflict with an@ \
               axiomatic with the same name in the E-ACSL runtime library,@ \
               please rename it.@]"
              name
        end;
        in_user_prj
      in
      let assoc _g =
        List.iter
          (fun li ->
             let lv_name = li.l_var_info.lv_name in
             let old_lis = Logic_env.Logic_info.find lv_name in
             let old_li =
               try
                 List.find
                   (fun old_li -> Logic_utils.is_same_logic_info li old_li)
                   old_lis
               with Not_found ->
                 Options.fatal
                   "Unable to find the logic_info in the user's AST \
                    corresponding to the logic_info %a in the RTL's AST. This \
                    most likely comes from a mismatch between the axiomatic %s \
                    in the RTL that is supposed to mirror one from the stdlib."
                   Printer.pp_logic_info li
                   name
             in
             Assocs.add_li li old_li)
          fun_or_preds
      in
      do_it ~assoc mem acc l g
    | GAnnot _ :: l ->
      (* ignoring other annotations from the AST *)
      do_globals acc l
    | GPragma _ as g :: l ->
      do_it Symbols.mem_global acc l g
    | GAsm _ | GText _ as g :: _l  ->
      Options.fatal "unexpected global %a" Printer.pp_global g
  in
  do_globals [] rtl_ast.globals

(** [get_kf vi] returns the kernel function corresponding to the given varinfo
    in the current project. The varinfo must correspond to a kernel function. *)
let get_kf vi =
  try
    Globals.Functions.get vi
  with Not_found ->
    Options.fatal "unknown function %s in project %a"
      vi.vname
      Project.pretty (Project.current ())

(** [get_formals_and_spec prj vi] returns a couple with the formals and function
    specification of the function corresponding to the varinfo [vi] in the
    project [prj]. The varinfo must correspond to a function of the given
    project. *)
let get_formals_and_spec prj vi =
  let selection =
    State_selection.of_list
      [ Globals.Functions.self; Annotations.funspec_state ]
  in
  Project.on
    prj
    ~selection
    (fun vi ->
       let kf = get_kf vi in
       Kernel_function.get_formals kf,
       Annotations.funspec ~populate:false kf)
    vi

(** Visitor to replace [varinfo] and [logic_info] leaves of an AST with
    corresponding values from the [Assocs] tables.
    If the visitor is created with the [formals] associating the [varinfo] of
    the RTL formals with the [varinfo] of the user formals, then replace the
    corresponding [varinfo] leaves. *)
class vis_replace_leaves ?formals () =
  object
    (* Since we are already working on a copied project, we can use an inplace
       visitor. *)
    inherit Visitor.frama_c_inplace

    val formals: varinfo Varinfo.Hashtbl.t =
      match formals with
      | None -> Varinfo.Hashtbl.create 7
      | Some formals -> formals

    (* Since the RTL project will be deleted at the end of the AST
        merge, we can temporarily violate the Frama-C invariant that says
        that a varinfo or logic_info must be in a single project and directly
        replace the varinfo/logic_info of the RTL in the specification with the
        logic_info/varinfo of the user's AST. *)

    method! vlogic_info_use rtl_li =
      try
        (* Replace the logic_info if it is a logic_info from the RTL project. *)
        let user_li = Assocs.find_li rtl_li in
        Cil.ChangeTo user_li
      with Not_found ->
        Cil.SkipChildren

    method! vvrbl rtl_vi =
      try
        (* Replace the varinfo if it is a global from the RTL project.*)
        let user_vi = Assocs.find_vi rtl_vi in
        Cil.ChangeTo user_vi
      with Not_found ->
      try
        (* Replace the varinfo if it is a formal. *)
        let user_vi = Varinfo.Hashtbl.find formals rtl_vi in
        Cil.ChangeTo user_vi
      with Not_found ->
        (* Otherwise do nothing. *)
        Cil.SkipChildren
  end

(* [substitute_rtl_symbols] registers the correct symbols for RTL's functions *)
let substitute_rtl_symbols rtl_prj = function
  | GVarDecl _ | GVar _ as g ->
    g
  | GFunDecl(_, vi, loc) | GFun({ svar = vi }, loc) as g ->
    (* get the RTL's formals and spec *)
    let formals, spec = get_formals_and_spec rtl_prj vi in
    (match g with
     | GFunDecl _ ->
       Globals.Functions.replace_by_declaration spec vi loc
     | GFun(fundec, _) ->
       Globals.Functions.replace_by_definition spec fundec loc
     | _ -> assert false);
    (* [Globals.Functions.replace_by_declaration] assigns new vids to formals:
       get them back to their original ids in order to have the correct ids in
       [spec] *)
    let kf = get_kf vi in
    List.iter2
      (fun rtl_vi src_vi -> src_vi.vid <- rtl_vi.vid)
      formals
      (Kernel_function.get_formals kf);
    Cil.unsafeSetFormalsDecl vi formals;
    Annotations.register_funspec ~emitter:Options.emitter kf;
    Symbols.add_kf kf;
    g
  | GAnnot (Daxiomatic _ as ga, loc) ->
    let vis_replace_leaves = new vis_replace_leaves () in
    let ga = Visitor.visitFramacAnnotation vis_replace_leaves ga in
    Annotations.add_global Options.emitter ga;
    GAnnot (ga, loc)
  | GType _ | GCompTag _ | GCompTagDecl _ | GEnumTag _ | GEnumTagDecl _
  | GAnnot _ | GAsm _ | GPragma _ | GText _ ->
    assert false

(* [merge_rtl_spec rtl_prj rtl_global] adds the spec of the given global
   function from the RTL project to the corresponding function in the current
   project. Before adding the spec, the varinfos of the global variables and
   formals in the spec are replaced with their corresponding varinfos in the
   current project. *)
let merge_rtl_spec rtl_prj rtl_global =
  match rtl_global with
  | GFunDecl(_, vi, _loc) | GFun({ svar = vi }, _loc) as g ->
    (* get the RTL's formals and spec *)
    let rtl_formals, spec = get_formals_and_spec rtl_prj vi in
    (* if the spec is not empty, then merge it with the user's spec *)
    if not (Cil.is_empty_funspec spec) then begin
      (* get the user's kf *)
      let user_kf = Assocs.get_kf g in
      (* get the user's formals *)
      let user_formals = Kernel_function.get_formals user_kf in
      (* replace all the formals and global variables in the spec with the
         formals and globals from the user's project. *)
      let formals_assoc: varinfo Varinfo.Hashtbl.t = Varinfo.Hashtbl.create 7 in
      List.iter2
        (fun rtl_vi user_vi -> Varinfo.Hashtbl.add formals_assoc rtl_vi user_vi)
        rtl_formals
        user_formals;
      let vis_replace_formals = new vis_replace_leaves ~formals:formals_assoc () in
      let spec = Visitor.visitFramacFunspec vis_replace_formals spec in
      (* Add the updated spec to the user's kf *)
      Annotations.add_spec Options.emitter user_kf spec
    end
  | GVarDecl _ | GVar _ | GType _ | GCompTag _ | GCompTagDecl _ | GEnumTag _
  | GEnumTagDecl _ | GAnnot _ | GAsm _ | GPragma _ | GText _ ->
    assert false

(* [insert_rtl_globals] adds the rtl symbols into the user's AST *)
let insert_rtl_globals rtl_prj rtl_globals ast =
  let add_ty acc old_g new_g =
    let g = if Symbols.mem_global old_g then old_g else new_g in
    (* keep them in the AST even if already in the user's one to prevent forward
       references *)
    g :: acc
  in
  let rec add acc = function
    | [] ->
      acc
    | GType _ | GCompTagDecl _ | GEnumTagDecl _ as g :: l ->
      (* RTL types contain no libc values: no need to substitute inside them *)
      let acc = add_ty acc g g in
      add acc l
    | GCompTag(ci, loc) as g :: l ->
      (* RTL's structure definitions that are already defined in the AST shall
         be only declared *)
      let acc = add_ty acc g (GCompTagDecl(ci, loc)) in
      add acc l
    | GEnumTag(ei, loc) as g :: l ->
      (* RTL's enum definitions that are already defined in the AST shall be
         only declared *)
      let acc = add_ty acc g (GEnumTagDecl(ei, loc)) in
      add acc l
    | GVarDecl _ | GVar _ | GFunDecl _ | GFun _
    | GAnnot (Daxiomatic _, _) as g :: l ->
      let acc =
        if Symbols.mem_global g then
          (* The symbol is in the RTL project, but not in the user's project.
             Perform the symbols substitution and add the global to the user's
             project. *)
          let g = substitute_rtl_symbols rtl_prj g in
          g :: acc
        else if Assocs.mem_kf g then begin
          (* The symbol is in the RTL project and associated with a kf in the
             user's project. Merge both contracts. *)
          merge_rtl_spec rtl_prj g;
          acc
        end else
          acc
      in
      add acc l
    | GPragma _ as g :: l ->
      add (g :: acc) l
    | GAnnot _ | GAsm _ | GText _ as g :: _l  ->
      Options.fatal "unexpected global %a" Printer.pp_global g
  in
  ast.globals <- add ast.globals rtl_globals

let link rtl_prj =
  Options.feedback ~level:2 "link the E-ACSL RTL with the user source code";
  let rtl_ast = create_rtl_ast rtl_prj in
  let ast = Ast.get () in
  let rtl_globals = lookup_rtl_globals rtl_ast in
  (* Symbols._debug (); *)
  insert_rtl_globals rtl_prj rtl_globals ast;
  Assocs.clear ();
  Ast.mark_as_grown ()

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
