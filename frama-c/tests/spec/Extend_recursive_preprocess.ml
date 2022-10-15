open Logic_ptree
open Logic_const
open Cil_types

let ext_typing_fooo _typing_context _loc l =
  let type_lexpr = function
    | { lexpr_node = PLapp("gl_foo_ok", [], [ _ ]) } -> ptrue
    | { lexpr_node = PLapp("gl_foo_ko", [], [ _ ]) } -> pfalse
    | _ -> assert false
  in
  Cil_types.Ext_preds (List.map type_lexpr l)

let ext_typing_block typing_context loc_here node =
  match node.extended_node with
  | Ext_lexpr (name,data)  ->
    let status,kind = Logic_typing.get_typer name ~typing_context ~loc:node.extended_loc data in
    Logic_const.new_acsl_extension name loc_here status kind
  | Ext_extension (name, id, data) ->
    let status,kind = Logic_typing.get_typer_block name ~typing_context ~loc:node.extended_loc (id,data) in
    Logic_const.new_acsl_extension name loc_here status kind

let  ext_typing_foo typing_context loc (s,d) =
  let block = List.map (ext_typing_block typing_context loc) d in
  Cil_types.Ext_annot (s,block)

let preprocess_fooo_ptree_element = function
  | { lexpr_node = PLapp("must_replace", [], [ v ]) } as x ->
    { x with lexpr_node = PLapp("gl_foo" ^ "_ok", [], [ v ]) }
  | { lexpr_node = PLapp("must_not_replace", [], [ v ]) } as x ->
    { x with lexpr_node = PLapp("gl_foo" ^ "_ko", [], [ v ]) }
  | _ -> assert false

let preprocess_fooo_ptree = List.map preprocess_fooo_ptree_element

let preprocess_foo_ptree (id,data) = (id ^ "_ok",data)

let ext_fooo_visitor vis ext =
  let aux p = unamed (Pand(p,p)) in
  match ext with
  | Ext_preds pred ->
    if Visitor_behavior.is_copy vis#behavior then
      Cil.ChangeTo (Ext_preds (List.map aux pred))
    else
      Cil.DoChildren
  | _ -> assert false

let ext_foo_visitor vis ext =
  match ext with
  | Ext_annot _ ->
    if Visitor_behavior.is_copy vis#behavior then
      Cil.DoChildrenPost (fun ext ->
          match ext with
          | Ext_annot(s, l) -> Ext_annot(s ^ "_ok", l)
          | _ -> ext)
    else
      Cil.DoChildren
  | _ -> assert false

let ext_fooo_printer prt fmt ext =
  match ext with
  | Ext_preds ps ->
    Pretty_utils.pp_list ~pre:"@[data:" ~sep:",@ " prt#predicate fmt ps
  | _ -> assert false

let () =  Acsl_extension.register_global
    "gl_fooo" ~preprocessor:preprocess_fooo_ptree ext_typing_fooo
    ~printer:ext_fooo_printer ~visitor:ext_fooo_visitor false ;
  Acsl_extension.register_global_block
    "gl_foo" ~preprocessor:preprocess_foo_ptree ext_typing_foo
                              ~visitor:ext_foo_visitor false

let run () =
  let old = Project.current () in
  let vis prj = new Visitor.frama_c_copy prj in
  let final_project =
    File.create_project_from_visitor ~reorder:true "Test" vis
  in
  Project.set_current final_project;
  File.pretty_ast ();
  Filecheck.check_ast "Test";
  Project.set_current old

let () = Db.Main.extend run
