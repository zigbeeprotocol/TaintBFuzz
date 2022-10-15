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

open Cvalue

let restrict_float ~assume_finite fkind value =
  let truth = Cvalue_forward.assume_not_nan ~assume_finite fkind value in
  match truth with
  | `True -> value
  | `Unknown reduced_value -> reduced_value
  | `False -> Cvalue.V.bottom
  | _ -> assert false

(* Alarms should be handled by the preconditions of the builtin. This function
   only removes the forbidden floating-point values. *)
let remove_special_float fk value =
  match Kernel.SpecialFloat.get () with
  | "none"       -> value
  | "nan"        -> restrict_float ~assume_finite:false fk value
  | "non-finite" -> restrict_float ~assume_finite:true fk value
  | _            -> assert false

let arity2 fk caml_fun _state actuals =
  match actuals with
  | [_, arg1; _, arg2] ->
    let r =
      try
        let i1 = Cvalue.V.project_ival arg1 in
        let f1 = Ival.project_float i1 in
        let i2 = Cvalue.V.project_ival arg2 in
        let f2 = Ival.project_float i2 in
        let f' = Cvalue.V.inject_float (caml_fun (Fval.kind fk) f1 f2) in
        remove_special_float fk f'
      with Cvalue.V.Not_based_on_null ->
        Cvalue.V.topify_arith_origin (V.join arg1 arg2)
    in
    let result = if V.is_bottom r then [] else [r] in
    Builtins.Result result
  | _ -> raise (Builtins.Invalid_nb_of_args 2)

let register_arity2 c_name fk f =
  let name = "Frama_C_" ^ c_name in
  let replace = c_name in
  let t = Cil_types.TFloat (fk, []) in
  let typ () = t, [t; t] in
  Builtins.register_builtin name ~replace ~typ Cacheable (arity2 fk f)

let () =
  let open Fval in
  register_arity2 "atan2" Cil_types.FDouble atan2;
  register_arity2 "atan2f" Cil_types.FFloat atan2;
  register_arity2 "pow" Cil_types.FDouble pow;
  register_arity2 "powf" Cil_types.FFloat pow;
  register_arity2 "fmod" Cil_types.FDouble fmod;
  register_arity2 "fmodf" Cil_types.FFloat fmod

let arity1 name fk caml_fun _state actuals =
  match actuals with
  | [_, arg] ->
    let r =
      try
        let i = Cvalue.V.project_ival arg in
        let f = Ival.project_float i in
        let f' = Cvalue.V.inject_float (caml_fun (Fval.kind fk) f) in
        remove_special_float fk f'
      with
      | Cvalue.V.Not_based_on_null ->
        if Cvalue.V.is_bottom arg then begin
          V.bottom
        end else begin
          Self.result ~once:true ~current:true
            "function %s applied to address" name;
          Cvalue.V.topify_arith_origin arg
        end
    in
    let result = if V.is_bottom r then [] else [r] in
    Builtins.Result result
  | _ -> raise (Builtins.Invalid_nb_of_args 1)

let register_arity1 c_name fk f =
  let name = "Frama_C_" ^ c_name in
  let replace = c_name in
  let t = Cil_types.TFloat (fk, []) in
  let typ () = t, [t] in
  Builtins.register_builtin name ~replace ~typ Cacheable (arity1 name fk f)

let () =
  let open Fval in
  register_arity1 "cos" Cil_types.FDouble cos;
  register_arity1 "sin" Cil_types.FDouble sin;
  register_arity1 "acos" Cil_types.FDouble acos;
  register_arity1 "asin" Cil_types.FDouble asin;
  register_arity1 "atan" Cil_types.FDouble atan;
  register_arity1 "log" Cil_types.FDouble log;
  register_arity1 "log10" Cil_types.FDouble log10;
  register_arity1 "exp" Cil_types.FDouble exp;
  register_arity1 "sqrt" Cil_types.FDouble sqrt;
  register_arity1 "floor" Cil_types.FDouble floor;
  register_arity1 "ceil" Cil_types.FDouble ceil;
  register_arity1 "trunc" Cil_types.FDouble trunc;
  register_arity1 "round" Cil_types.FDouble fround;

  register_arity1 "cosf" Cil_types.FFloat cos;
  register_arity1 "sinf" Cil_types.FFloat sin;
  register_arity1 "acosf" Cil_types.FFloat acos;
  register_arity1 "asinf" Cil_types.FFloat asin;
  register_arity1 "atanf" Cil_types.FFloat atan;
  register_arity1 "logf" Cil_types.FFloat log;
  register_arity1 "log10f" Cil_types.FFloat log10;
  register_arity1 "expf" Cil_types.FFloat exp;
  register_arity1 "sqrtf" Cil_types.FFloat sqrt;
  register_arity1 "floorf" Cil_types.FFloat floor;
  register_arity1 "ceilf" Cil_types.FFloat ceil;
  register_arity1 "truncf" Cil_types.FFloat trunc;
  register_arity1 "roundf" Cil_types.FFloat fround
