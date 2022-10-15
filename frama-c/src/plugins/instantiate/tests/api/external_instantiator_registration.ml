let function_name = "mine"

let well_typed_call _ _ = function
  | [ e ] ->
    let t = Cil.typeOf(Cil.stripCasts e) in
    not (Cil.isVoidPtrType t) && Cil.isPointerType t
  | _ -> false

let key_from_call _ _ = function
  | [ e ] ->
    let t = Cil.typeOf(Cil.stripCasts e) in
    Cil.typeOf_pointed t
  | _ -> assert false

let retype_args _ = function
  | [ e ] -> [ Cil.stripCasts e ]
  | _ -> assert false

let generate_function_type t =
  let params = [
    ("x", Cil_types.TPtr(t, []), [])
  ] in
  Cil_types.TFun(Cil.voidType, Some params, false, [])

let generate_prototype t =
  let fun_type = generate_function_type t in
  let name = function_name ^ "_" ^ match t with
    | Cil_types.TInt(_) -> "int"
    | Cil_types.TFloat(_) -> "float"
    | _ -> assert false (* nothing else in our test *)
  in
  name, fun_type

let generate_spec _ _ _ = Cil.empty_funspec ()

let args_for_original _ x = x

let () = Instantiate.Transform.register (module struct
    module Hashtbl = Cil_datatype.Typ.Hashtbl
    type override_key = Hashtbl.key

    let function_name = function_name
    let well_typed_call = well_typed_call
    let key_from_call = key_from_call
    let retype_args = retype_args
    let generate_prototype = generate_prototype
    let generate_spec = generate_spec
    let args_for_original = args_for_original
  end)
