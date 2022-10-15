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

open Cil_types
open Options
module List = Extends.List
module Typ = Extends.Typ
module Build = Cil_builder.Pure


(* Types of variadic parameter and argument *)

let vpar_typ attr =
  TPtr (TPtr (TVoid [], [Attr ("const", [])]), attr)
let vpar_name = "__va_params"
let vpar =
  (vpar_name, vpar_typ [], [])


(* Translation of variadic types (not deeply) *)

let translate_type = function
  | TFun (ret_typ, args, is_variadic, attributes) ->
    let new_args =
      if is_variadic
      then
        let ng_args, g_args = Cil.argsToPairOfLists args in
        Some (ng_args @ [vpar] @ g_args)
      else args
    in
    TFun (ret_typ, new_args, false, attributes)

  | TBuiltin_va_list attr -> vpar_typ attr

  | typ -> typ


(* Adding the vpar parameter to variadic functions *)

let add_vpar vi =
  let formals = Cil.getFormalsDecl vi in
  let n_formals, g_formals = List.partition (fun v -> not v.vghost) formals in
  (* Add the vpar formal once *)
  if not (List.exists (fun vi -> vi.vname = vpar_name) formals) then
    begin
      (* Register the new formal *)
      let new_formal = Cil.makeFormalsVarDecl vpar in
      let new_formals = n_formals @ [new_formal] @ g_formals in
      Cil.unsafeSetFormalsDecl vi new_formals
    end


(* Translation of va_* builtins  *)

let translate_va_builtin caller inst =
  let vi, args, loc = match inst with
    | Call(_, {enode = Lval(Var vi, _)}, args, loc) ->
      vi, args, loc
    | _ -> assert false
  in

  let translate_va_start () =
    let va_list = match args with
      | [{enode=Lval va_list}] -> va_list
      | _ -> Self.fatal "Unexpected arguments to va_start"
    and varg =
      try Extlib.last (Cil.getFormalsDecl caller.svar)
      with Invalid_argument _ ->
        Self.abort "Using va_start macro in a function which is not variadic."
    in
    [ Set (va_list, Cil.evar ~loc varg, loc) ]
  in

  let translate_va_copy () =
    let dest, src = match args with
      | [{enode=Lval dest}; src] -> dest, src
      | _ -> Self.fatal "Unexpected arguments to va_copy"
    in
    [ Set (dest, src, loc) ]
  in

  let translate_va_arg () =
    let va_list, ty, lv = match args with
      | [{enode=Lval va_list};
         {enode=SizeOf ty};
         {enode=CastE(_, {enode=AddrOf lv})}] -> va_list, ty, lv
      | _ -> Self.fatal "Unexpected arguments to va_arg"
    in
    (* Check validity of type *)
    if Cil.isIntegralType ty then begin
      let promoted_type = Cil.integralPromotion ty in
      if promoted_type <> ty then
        Self.warning ~current:true ~wkey:wkey_typing
          "Wrong type argument in va_start: %a is promoted to %a when used \
           in the variadic part of the arguments. (You should pass %a to \
           va_start)"
          Printer.pp_typ ty
          Printer.pp_typ promoted_type
          Printer.pp_typ promoted_type
    end;
    (* Build the replacing instruction *)
    let va_list, ty, lv = Build.(of_lval va_list, of_ctyp ty, of_lval lv) in
    List.map (Build.cil_instr ~loc) Build.([
        lv := mem (cast (ptr ty) (mem va_list));
        va_list += of_int 1
      ])
  in

  begin match vi.vname with
    | "__builtin_va_start" -> translate_va_start ()
    | "__builtin_va_copy" -> translate_va_copy ()
    | "__builtin_va_arg" -> translate_va_arg ()
    | "__builtin_va_end" -> [] (* No need to do anything for va_end *)
    | _ -> assert false
  end


(* Translation of calls to variadic functions *)

let translate_call ~fundec ~ghost block loc mk_call callee pars =
  (* Log translation *)
  Self.result ~current:true ~level:2
    "Generic translation of call to variadic function.";

  (* Split params into static, variadic and ghost part *)
  let ng_params, g_params = Typ.ghost_partitioned_params (Cil.typeOf callee) in
  let static_size = List.length ng_params - 1 in
  let s_exps, r_exps = List.break static_size pars in
  let variadic_size = (List.length r_exps) - (List.length g_params) in
  let v_exps, g_exps = List.break variadic_size r_exps in

  (* Start build *)
  let module Build = Cil_builder.Stateful (struct let loc = loc end) in
  Build.open_block ~into:fundec ~ghost ();

  (* Create temporary variables to hold parameters *)
  let add_var i e =
    let name = "__va_arg" ^ string_of_int i in
    Build.(local' (Cil.typeOf e) name ~init:(of_exp e))
  in
  let vis = List.mapi add_var v_exps in

  (* Build an array to store addresses *)
  let init = match vis with (* C standard forbids arrays of size 0 *)
    | [] -> [Build.of_init (Cil.makeZeroInit ~loc Cil.voidPtrType)]
    | l -> List.map Build.addr l
  in
  let ty = Build.(array (ptr void) ~size:(List.length init)) in
  let vargs = Build.(local ty "__va_args" ~init) in

  (* Translate the call *)
  let new_arg = Build.(cil_exp ~loc (cast' (vpar_typ []) (addr vargs))) in
  let new_args = (s_exps @ [new_arg] @ g_exps) in
  Build.of_instr (mk_call callee new_args);
  Build.finish_instr_list ~scope:block ()
