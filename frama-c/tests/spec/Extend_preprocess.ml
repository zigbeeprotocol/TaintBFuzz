open Logic_ptree
open Logic_const

(* For each kind of extension:
   - behavior:        bhv
   - next loop:       nl
   - code annotation: ca
   - next statement:  ns
   - global:          gl
  replaces node "must_replace(x)" with "<kind>_ok(x)". The typing phase
  validates that we find the right "<kind>_ok" for each kind of extension:
   - if a must_replace is found, it fails,
   - if the wrong kind is found, a "\false" is generated
   - if everything is ok "\true" is generated
*)

let validate kind call =
  assert (not (String.equal "must_replace" call)) ;
  match String.split_on_char '_' call with
  | [ lkind ; lok ] -> String.equal kind lkind && String.equal lok "ok"
  | _ -> false

let ext_typing kind typing_context loc l =
  let _ = loc in
  let _ = typing_context in
  let type_lexpr = function
    | { lexpr_node = PLapp(s, [], [ _ ]) } when validate kind s -> ptrue
    | _ -> pfalse
  in
  Cil_types.Ext_preds (List.map type_lexpr l)

let preprocess_foo_ptree_element kind = function
  | { lexpr_node = PLapp("must_replace", [], [ v ]) } as x ->
    { x with lexpr_node = PLapp(kind ^ "_ok", [], [ v ]) }
  | x -> x

let preprocess_foo_ptree kind = List.map (preprocess_foo_ptree_element kind)

let register registration ?visitor ?printer ?short_printer kind =
  let registration ?preprocessor typer =
    registration
      (kind ^ "_foo") ?preprocessor typer ?visitor ?printer ?short_printer false
  in
  registration ~preprocessor:(preprocess_foo_ptree kind) (ext_typing kind)


let () =
  let open Acsl_extension in
  register register_behavior "bhv";
  register register_code_annot_next_loop "nl";
  register register_code_annot "ca";
  register register_code_annot_next_stmt "ns";
  register register_global "gl"
