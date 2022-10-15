open Logic_ptree
open Logic_typing
open Cil_types

let preprocessor =
  List.map (fun e -> begin match e with
      | { lexpr_node = PLnamed ("load", { lexpr_node = PLvar s}) } ->
        if not (Logic_env.is_logic_type s) then Logic_env.add_typename s
        else Kernel.error "Type already exists %s" s
      | _ -> ()
    end ; e)

module Ts = struct
  let id = ref 0
  let types = Hashtbl.create 5

  let add t = let i = !id in Hashtbl.add types i t ; id := i + 1 ; i
  let find = Hashtbl.find types
end

let typer ctxt loc = function
  | [ { lexpr_node = PLnamed ("load", { lexpr_node = PLvar s}) } ] ->
    let ti = { lt_name = s ; lt_params = [] ; lt_def = None ; lt_attr = []} in
    ctxt.add_logic_type s ti ;
    Ext_id (Ts.add ti)
  | _ ->
    ctxt.error loc "Expected type loader"

let visitor _ _ = Cil.SkipChildren

let gen_printer s _pp fmt = function
  | Ext_id i ->
    Format.fprintf fmt "%s: %s"
      (if s then "ext_type" else "load") (Ts.find i).lt_name
  | _ -> assert false

let printer = gen_printer false
let short_printer = gen_printer true

let () =
  Acsl_extension.register_global
    "ext_type" ~preprocessor typer ~visitor ~printer ~short_printer false