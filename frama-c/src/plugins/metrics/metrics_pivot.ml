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

(* Data for a GUI-based pivot table *)

open Cil_types

module PivotSourceState =
  State_builder.List_ref
    (Datatype.List(Datatype.String))
    (struct
      let name = "PivotSourceState"
      let dependencies = [ Ast.self; Eva.Analysis.self; Property_status.self;
                           Messages.self ]
    end)

type syntax_domain =
  | Code
  | Declaration
  | Annotation

type message_domain = Log.kind

type domain =
  | Syntax of syntax_domain
  | Property
  | Message of message_domain

let string_of_string_list sep =
  Format.asprintf "%a"
    (Pretty_utils.pp_list ~pre:"" ~suf:"" ~sep Format.pp_print_string)

let split_loc (loc : Cil_types.location) =
  let fp = (fst loc).pos_path in
  let line = string_of_int (fst loc).pos_lnum in
  let fp_pretty = Filepath.Normalized.to_pretty_string fp in
  let dir = Filename.dirname fp_pretty in
  let name = Filename.basename fp_pretty in
  let ext = Filename.extension name in
  dir, name, ext, line

let node_of_instr = function
  | Set _ -> "assignment"
  | Call _ -> "call"
  | Local_init _ -> "local_init"
  | Asm _ -> "asm"
  | Skip _ -> "nop"
  | Code_annot _ ->
    (* should be done by the annotations visitor *)
    assert false

let opt_node_of_stmtkind = function
  | Instr _ -> None
  | Return (_, _) -> Some "return"
  | Goto (_, _) -> Some "goto"
  | Break _ -> Some "break"
  | Continue _ -> Some "continue"
  | If (_, _, _, _) -> Some "if"
  | Switch (_, _, _, _) -> Some "switch"
  | Loop (_, _, _, _, _) -> Some "loop"
  | Block _ -> None
  | UnspecifiedSequence _ -> Some "unspecified_sequence"
  | Throw (_, _) -> Some "throw"
  | TryCatch (_, _, _) -> Some "try_catch"
  | TryFinally (_, _, _) -> Some "try_finally"
  | TryExcept (_, _, _, _) -> Some "try_except"

let node_of_code_annotation_node = function
  | AAssert _ -> "assert"
  | AStmtSpec _ -> "stmt_spec"
  | AInvariant _ -> "invariant"
  | AVariant _ -> "variant"
  | AAssigns _ -> "assigns"
  | AAllocation _ -> "allocation"
  | APragma _ -> "ca_pragma"
  | AExtended _ -> "extended"

let node_of_global_annotation = function
  | Dfun_or_pred _ -> "logic_fun_or_pred"
  | Dvolatile _ ->  "logic_volatile"
  | Daxiomatic _ -> "axiomatic"
  | Dtype _ -> "logic_type"
  | Dlemma _ -> "logic_lemma"
  | Dinvariant _ -> "invariant"
  | Dtype_annot _ -> "type_annot"
  | Dmodel_annot _ -> "model_annot"
  | Dextended _ -> "ga_extended"

let domain_and_node_of_global = function
  | GType _ -> Declaration, "gtype"
  | GCompTag _ -> Declaration, "gcomptag"
  | GCompTagDecl _ -> Declaration, "gcomptagdecl"
  | GEnumTag _ -> Declaration, "genumtag"
  | GEnumTagDecl _ -> Declaration, "genumtagdecl"
  | GVarDecl _ -> Declaration, "global_var"
  | GFunDecl _ -> Declaration, "gfundecl"
  | GVar _ -> Declaration, "gvar"
  | GFun _ -> Declaration, "gfun"
  | GAsm _ -> Code, "gasm"
  | GPragma _ -> Code, "gpragma"
  | GText _ -> Code, "gtext"
  | GAnnot _ -> Code, "gannot"

let names_of_global = function
  | GType (_, _) -> []
  | GCompTag (_, _) -> []
  | GCompTagDecl (_, _) -> []
  | GEnumTag (_, _) -> []
  | GEnumTagDecl (_, _) -> []
  | GVarDecl (vi, _) -> [vi.vname]
  | GFunDecl (_, vi, _) -> [vi.vname]
  | GVar (vi, _, _) -> [vi.vname]
  | GFun ({svar}, _) -> [svar.vname]
  | GAsm (_, _) -> []
  | GPragma (_, _) -> []
  | GText _ -> []
  | GAnnot (_, _) -> []

let name_of_logic_info li = li.l_var_info.lv_name

let name_of_global_annotation = function
  | Dvolatile (_, _, _, _, _) -> None
  | Dfun_or_pred (li, _)
  | Dinvariant (li, _)
  | Dtype_annot (li, _) -> Some (name_of_logic_info li)
  | Daxiomatic (name, _, _, _)
  | Dtype ({lt_name = name}, _)
  | Dlemma (name, _, _, _, _, _)
  | Dmodel_annot ({mi_name = name}, _)
  | Dextended ({ext_name = name}, _, _) -> Some name

let node_of_predicate_kind = function
  | Assert -> "assert"
  | Check -> "check"
  | Admit -> "admit"

let node_of_property = function
  | Property.IPPredicate idp ->
    Format.asprintf "%a" Property.pretty_predicate_kind idp.ip_kind
  | IPCodeAnnot ica -> node_of_code_annotation_node ica.ica_ca.annot_content
  | IPAxiomatic _ -> "axiomatic"
  | IPLemma _ -> "lemma"
  | IPBehavior _ -> "behavior"
  | IPComplete _ -> "complete"
  | IPDisjoint _ -> "disjoint"
  | IPAllocation _ -> "allocates"
  | IPAssigns _ -> "assigns"
  | IPFrom _ -> "from"
  | IPDecrease _ -> "loop variant"
  | IPExtended _ -> "extended"
  | IPReachable _ -> "reachable"
  | IPPropertyInstance _ -> "instance"
  | IPTypeInvariant _ -> "type_invariant"
  | IPGlobalInvariant _ -> "global_invariant"
  | IPOther _ -> "other"

let names_of_property = function
  | Property.IPPredicate idp -> idp.ip_pred.ip_content.tp_statement.pred_name
  | IPCodeAnnot _ -> []
  | IPAxiomatic _ -> []
  | IPLemma _ -> []
  | IPBehavior _ -> []
  | IPComplete _ -> []
  | IPDisjoint _ -> []
  | IPAllocation _ -> []
  | IPAssigns _ -> []
  | IPFrom _ -> []
  | IPDecrease _ -> []
  | IPExtended _ -> []
  | IPReachable _ -> []
  | IPPropertyInstance _ -> []
  | IPTypeInvariant _ -> []
  | IPGlobalInvariant _ -> []
  | IPOther _ -> []

let plugin_of_emitters el =
  match el with
  | []
  | ["Call Preconditions"]
  | ["Frama-C kernel"] -> "kernel"
  | ["Eva"] -> "eva"
  | _ -> "<unknown emitters (" ^ string_of_string_list "," el ^ ")>"

let string_of_syntax_domain = function
  | Code -> "code"
  | Declaration -> "decl"
  | Annotation -> "annot"

let string_of_message_domain = function
  | Log.Result -> "result"
  | Feedback -> "feedback"
  | Debug -> "debug"
  | Warning ->  "warning"
  | Error -> "error"
  | Failure -> "failure"

let split_domain = function
  | Syntax d -> "syntax", string_of_syntax_domain d
  | Property -> "property", ""
  | Message d -> "message", string_of_message_domain d

module FunctionAtPos = struct
  let tbl :
    (Filepath.Normalized.t,
     (Filepath.position * Filepath.position * string) Array.t)
      Hashtbl.t =
    Hashtbl.create 16

  let binary_search a pos : string option =
    let cmp = Cil_datatype.Position.compare in
    let rec aux lo hi =
      if lo > hi then None
      else
        let mid = (hi + lo) / 2 in
        let (mstart, mend, mfunc) = a.(mid) in
        if cmp pos mstart >= 0 then
          if cmp pos mend <= 0 then Some mfunc
          else aux (mid + 1) hi
        else aux lo (mid - 1)
    in
    aux 0 (Array.length a - 1)

  let compute () =
    let tmp = Hashtbl.create 16 in
    let files =
      List.fold_left (fun acc ((pos1, _, _) as triple) ->
          let fp = pos1.Filepath.pos_path in
          Hashtbl.add tmp fp triple;
          Datatype.Filepath.Set.add fp acc
        ) Datatype.Filepath.Set.empty (Cabs2cil.func_locs ())
    in
    Hashtbl.clear tbl;
    Datatype.Filepath.Set.iter (fun fp ->
        let l =
          List.sort (fun (start1, _, _) (start2, _, _) ->
              Cil_datatype.Position.compare start1 start2
            ) (Hashtbl.find_all tmp fp)
        in
        Hashtbl.replace tbl fp (Array.of_list l)
      ) files

  let find pos =
    let fp = pos.Filepath.pos_path in
    Option.bind (Hashtbl.find_opt tbl fp)
      (fun a -> binary_search a pos)

end

type entry = {
  loc: Cil_datatype.Location.t;
  func: string option;
  domain: domain;
  plugin: string;
  status: string;
  node: string;
  names: string list;
  text: string;
}

let headers = ["Directory"; "Filename"; "Extension"; "Line Number";
               "Function"; "Domain"; "Kind"; "Plugin"; "Status"; "Node";
               "Names"; "Text"]

let add_entry_str entry =
  let dir, fname, ext, line = split_loc entry.loc in
  let funcname = Option.fold ~none:"" ~some:Stdlib.Fun.id entry.func in
  let domain, kind = split_domain entry.domain in
  let names = string_of_string_list ":" entry.names in
  let entry = [dir; fname; ext; line; funcname;
               domain; kind; entry.plugin; entry.status; entry.node;
               names; entry.text]
  in
  if PivotSourceState.get () = [] then
    PivotSourceState.add headers;
  PivotSourceState.add entry

let new_entry ?func ?(plugin="") ?(status="") ?(node="") ?(names=[]) ?(text="") loc domain =
  { loc; func; domain; plugin; status; node; names; text }

let add_entry ?func ?plugin ?status ?node ?names ?text loc domain =
  let entry = new_entry ?func ?plugin ?status ?node ?names ?text loc domain in
  add_entry_str entry

class full_visitor = object(self)
  inherit Cil.nopCilVisitor
  val mutable cur_func = None
  method add ?func ?node ?names domain =
    let loc = Cil.CurrentLoc.get () in
    let func = if func <> None && func <> Some "" then func else cur_func in
    add_entry ?func ?node ?names loc domain
  method add_code ?func ?names node =
    self#add ?func ~node ?names (Syntax Code)
  method add_decl ?func ?names node =
    self#add ?func ~node ?names (Syntax Declaration)
  method add_annot ?names node =
    self#add ~node ?names (Syntax Annotation)

  method! vvrbl (_v:varinfo) = Cil.DoChildren
  method! vvdec (_v:varinfo) = Cil.DoChildren
  method! vexpr (_e:exp) = Cil.DoChildren
  method! vlval (_l:lval) = Cil.DoChildren
  method! voffs (_o:offset) = Cil.DoChildren
  method! vinitoffs (_o:offset) = Cil.DoChildren

  method! vinst (i:instr) =
    let node = node_of_instr i in
    self#add_code node;
    Cil.DoChildren

  method! vstmt (s:stmt) =
    begin
      match opt_node_of_stmtkind s.skind with
      | None -> ()
      | Some node -> self#add_code node
    end;
    Cil.DoChildren

  method! vfunc (f:fundec) =
    cur_func <- Some f.svar.vname;
    Cil.DoChildrenPost (fun fd ->
        cur_func <- None;
        fd
      )

  method! vglob (g:global) =
    let domain, node = domain_and_node_of_global g in
    let names = names_of_global g in
    let func = "<global>" in
    if domain = Declaration then
      self#add_decl ~func ~names node
    else
      self#add_code ~func ~names node;
    Cil.DoChildren

  method! vblock _ = Cil.DoChildren
  method! vinit _ _ _ = Cil.DoChildren
  method! vlocal_init _ _ = Cil.DoChildren
  method! vtype _ = Cil.DoChildren
  method! vcompinfo _ = Cil.DoChildren
  method! venuminfo _ = Cil.DoChildren
  method! vfieldinfo _ = Cil.DoChildren
  method! venumitem _ = Cil.DoChildren
  method! vattr _ = Cil.DoChildren
  method! vattrparam _ = Cil.DoChildren
  method! vmodel_info _ = Cil.DoChildren
  method! vlogic_type _ = Cil.DoChildren
  method! videntified_term _ = Cil.DoChildren
  method! vterm _ = Cil.DoChildren
  method! vterm_node _ = Cil.DoChildren
  method! vterm_lval _ = Cil.DoChildren
  method! vterm_lhost _ = Cil.DoChildren
  method! vterm_offset _ = Cil.DoChildren
  method! vlogic_label _ = Cil.DoChildren
  method! vlogic_info_decl _ = Cil.DoChildren
  method! vlogic_info_use _ = Cil.DoChildren
  method! vlogic_type_info_decl _ = Cil.DoChildren
  method! vlogic_type_info_use _ = Cil.DoChildren
  method! vlogic_type_def _ = Cil.DoChildren
  method! vlogic_ctor_info_decl _ = Cil.DoChildren
  method! vlogic_ctor_info_use _ = Cil.DoChildren
  method! vlogic_var_use _ = Cil.DoChildren
  method! vlogic_var_decl _ = Cil.DoChildren
  method! vquantifiers _ = Cil.DoChildren
  method! videntified_predicate _ =
    (* should be done by the annotations visitor *)
    assert false
  method! vpredicate_node _ = Cil.DoChildren
  method! vpredicate _ = Cil.DoChildren
  method! vbehavior _ = Cil.DoChildren
  method! vassigns _ = Cil.DoChildren
  method! vfrees _ = Cil.DoChildren
  method! vallocates _ = Cil.DoChildren
  method! vallocation _ = Cil.DoChildren
  method! vloop_pragma _ = Cil.DoChildren
  method! vslice_pragma _ = Cil.DoChildren
  method! vimpact_pragma _ = Cil.DoChildren
  method! vdeps _ = Cil.DoChildren
  method! vfrom _ = Cil.DoChildren
  method! vcode_annot _ =
    (* should be done by the annotations visitor *)
    assert false
  method! vannotation ga =
    let node = node_of_global_annotation ga in
    let names = Option.to_list (name_of_global_annotation ga) in
    self#add_annot ~names node;
    Cil.DoChildren
end

let ca_visitor_cur_func : string option ref = ref None
let ca_visitor_cur_emitter = ref "<unknown>"
class code_annot_visitor = object(self)
  inherit Cil.nopCilVisitor

  method add_annot ?(names=[]) node =
    let loc = Cil.CurrentLoc.get () in
    let func = !ca_visitor_cur_func in
    let plugin = !ca_visitor_cur_emitter in
    let domain = Syntax Annotation in
    add_entry ?func ~plugin ~node ~names loc domain

  method! videntified_predicate {ip_content = {tp_kind}} =
    let node = node_of_predicate_kind tp_kind in
    self#add_annot node;
    Cil.DoChildren

  method! vcode_annot ca =
    let content = ca.annot_content in
    self#add_annot (node_of_code_annotation_node content);
    Cil.DoChildren

  method! vannotation ga =
    let node = node_of_global_annotation ga in
    let names = Option.to_list (name_of_global_annotation ga) in
    self#add_annot ~names node;
    Cil.DoChildren
end

let visit_annots () =
  let vis = new code_annot_visitor in
  Annotations.iter_all_code_annot (
    fun stmt emitter ca ->
      let kf = Kernel_function.find_englobing_kf stmt in
      ca_visitor_cur_func := Some (Kernel_function.get_name kf);
      ca_visitor_cur_emitter := Emitter.get_name emitter;
      ignore (Cil.visitCilCodeAnnotation (vis :> Cil.cilVisitor) ca)
  )

let visit_properties () =
  Property_status.iter
    (fun ip ->
       let loc = Property.location ip in
       let func = Option.map Kernel_function.get_name (Property.get_kf ip) in
       let emitters =
         Property_status.fold_on_statuses (fun emitter _status acc ->
             Emitter.Usable_emitter.get_name emitter.emitter :: acc
           ) ip []
       in
       let plugin = plugin_of_emitters emitters in
       let domain = Property in
       let status =
         Format.asprintf "%a"
           Property_status.Feedback.pretty (Property_status.Feedback.get ip)
       in
       let node = node_of_property ip in
       let names = names_of_property ip in
       add_entry ?func ~node ~status ~plugin ~names loc domain
    )

let visit_messages () =
  FunctionAtPos.compute ();
  Messages.iter (fun ev ->
      let plugin = ev.evt_plugin in
      let loc_of_pos p = (p, p) in
      let loc, func =
        match ev.evt_source with
        | None -> Cil_datatype.Location.unknown, "<global>"
        | Some pos ->
          let funcname =
            match FunctionAtPos.find pos with
            | None -> Metrics_parameters.warning
                        "FUNCTION NOT FOUND FOR NON-GLOBAL MESSAGE POS: %a"
                        Cil_datatype.Position.pretty_debug pos;
              "<unknown>"
            | Some name -> name
          in
          loc_of_pos pos, funcname
      in
      let domain = Message (ev.evt_kind) in
      let text = ev.evt_message in
      add_entry ~func ~plugin ~text loc domain
    )

(* Useful mainly for debugging *)
let _pp_as_csv (data : string list list) =
  let pp_list = string_of_string_list "," in
  List.iter (fun ls -> Format.printf "%s@\n" (pp_list ls)) (List.rev data)

(* Server / Ivette stuff *)

open Server

let package =
  Package.package
    ~plugin:"pivot"
    ~name:"general"
    ~title:"Pivot Table Services"
    ~readme:"pivot.md"
    ()

module TableState = struct
  type t = string list list
  let jtype =
    Data.declare ~package
      ~name:"tableStateType"
      ~descr:(Markdown.plain "State of the pivot table source data.")
      Package.(Jarray (Jarray Jstring))
  let to_json ll =
    `List (List.rev_map (fun l -> `List (List.map (fun s -> `String s) l)) ll)
end

let pivot_signal =
  States.register_value ~package
    ~name:"pivotState"
    ~descr:(Markdown.plain "State of the pivot table source data.")
    ~output:(module TableState)
    ~get:PivotSourceState.get
    ~add_hook:PivotSourceState.add_hook_on_update
    ()

let compute () =
  let ast = Ast.get () in
  let vis = new full_visitor in
  ignore (Cil.visitCilFile (vis :> Cil.cilVisitor) ast);
  visit_annots ();
  visit_properties ();
  visit_messages ();
  (*_pp_as_csv (PivotSourceState.get ());*)
  (* Signals that the pivot table has been updated. *)
  Server.Request.emit pivot_signal

let _compute =
  Server.Request.register ~package
    ~kind:`EXEC ~name:"compute"
    ~descr:(Markdown.plain "Computes the pivot table.")
    ~input:(module Data.Junit) ~output:(module Data.Junit) compute
