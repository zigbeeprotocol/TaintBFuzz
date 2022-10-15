open Logic_ptree
open Cil_types
open Logic_typing

let type_foo typing_context _loc l =
  let type_term ctxt env expr =
    match expr.lexpr_node with
      | PLvar "\\foo" -> Logic_const.tinteger ~loc:expr.lexpr_loc 42
      | _ -> typing_context.type_term ctxt env expr
  in
  let typing_context = { typing_context with type_term } in
  let res =
    List.map (typing_context.type_term typing_context (Lenv.empty())) l
  in
  Ext_terms res

let () = Acsl_extension.register_behavior "foo" type_foo false
