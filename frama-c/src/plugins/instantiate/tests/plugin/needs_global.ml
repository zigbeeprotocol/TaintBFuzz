let well_typed_call _ _ = function
  | [ e ] ->
    let t = Cil.typeOf(Cil.stripCasts e) in
    not (Cil.isVoidPtrType t) && Cil.isPointerType t
  | _ -> false

let key_from_call _ _ = function
  | [ e ] -> Cil.typeOf_pointed (Cil.typeOf(Cil.stripCasts e))
  | _ -> assert false

let retype_args _ = function
  | [ e ] -> [ Cil.stripCasts e ]
  | _ -> assert false

let generate_function_type t =
  let params = [("x", Cil_types.TPtr(t, []), [])] in
  Cil_types.TFun(Cil.voidType, Some params, false, [])

let generate_prototype function_name t =
  let fun_type = generate_function_type t in
  let name = function_name ^ "_" ^ match t with
    | Cil_types.TInt(_) -> "int"
    | _ -> assert false (* nothing else in our test *)
  in
  name, fun_type

let generate_spec needed _ _ _ =
  let open Cil_types in
  let open Logic_const in
  let open Instantiate.Global_context in
  let make () =
    let vi = Cil.makeVarinfo ~ghost:true true false needed Cil.floatType in
    vi.vstorage <- Extern ;
    vi
  in
  let vi = get_variable needed make in
  let t = tvar (Cil.cvar_to_lvar vi) in
  let assigns =
    Cil_types.Writes [ Logic_const.new_identified_term t, From [] ]
  in {
    spec_behavior = [ {
      b_name = Cil.default_behavior_name ;
      b_requires = [] ;
      b_assumes = [] ;
      b_post_cond = [] ;
      b_assigns = assigns ;
      b_allocation = FreeAllocAny ;
      b_extended = []
    } ] ;
    spec_variant = None ;
    spec_terminates = None ;
    spec_complete_behaviors = [] ;
    spec_disjoint_behaviors = [] ;
  }

let () = Instantiate.Transform.register (module struct
    module Hashtbl = Cil_datatype.Typ.Hashtbl
    type override_key = Hashtbl.key

    let function_name = "already_one"
    let well_typed_call = well_typed_call
    let key_from_call = key_from_call
    let retype_args = retype_args
    let generate_prototype = generate_prototype function_name
    let generate_spec = generate_spec "i"
    let args_for_original _ = Extlib.id
  end)

let () = Instantiate.Transform.register (module struct
    module Hashtbl = Cil_datatype.Typ.Hashtbl
    type override_key = Hashtbl.key

    let function_name = "needs_new"
    let well_typed_call = well_typed_call
    let key_from_call = key_from_call
    let retype_args = retype_args
    let generate_prototype = generate_prototype function_name
    let generate_spec = generate_spec "j"
    let args_for_original _ = Extlib.id
  end)
