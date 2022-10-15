open Logic_typing
open Cil_types

let load_theory = function
  | { pred_content = Papp (_, [], [ { term_node = TConst(LStr _name) } ] ) } ->
    raise Not_found
  | _ -> assert false

let typer typing_context loc lexprs =
  ignore loc ;
  let type_predicate =
    typing_context.type_predicate typing_context (Lenv.empty ())
  in
  let predicates = List.map type_predicate lexprs in
  List.iter load_theory predicates ;
  Ext_preds predicates


let () =
  Acsl_extension.register_global "why3" typer false

let main () =
  try
    Kernel.feedback
      "Checking handler of exception occurring in extension typing";
    Ast.compute (); assert false
  with
    | Log.AbortFatal _ -> Kernel.feedback "Extension typing failed as expected"
    | Not_found -> Kernel.fatal "kernel did not capture our exception"
    | Assert_failure _ -> Kernel.fatal "kernel silently captured our exception"

let () = Kernel.TypeCheck.set false

let () = Kernel.Debug.set 1

let () = Db.Main.extend main
