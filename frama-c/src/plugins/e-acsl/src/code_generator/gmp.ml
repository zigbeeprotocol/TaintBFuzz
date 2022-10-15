(**************************************************************************)
(*                                                                        *)
(*  This file is part of the Frama-C's E-ACSL plug-in.                    *)
(*                                                                        *)
(*  Copyright (C) 2012-2021                                               *)
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
module Error = Translation_error

(**************************************************************************)
(************************* Calls to builtins ******************************)
(**************************************************************************)

let apply_on_var ~loc funname e =
  let prefix =
    let ty = Cil.typeOf e in
    if Gmp_types.Z.is_t ty then "__gmpz_"
    else if Gmp_types.Q.is_t ty then "__gmpq_"
    else assert false
  in
  Smart_stmt.rtl_call ~loc ~prefix funname [ e ]

let name_of_mpz_arith_bop = function
  | PlusA -> "__gmpz_add"
  | MinusA -> "__gmpz_sub"
  | Mult -> "__gmpz_mul"
  | Div -> "__gmpz_tdiv_q"
  | Mod -> "__gmpz_tdiv_r"
  | BAnd -> "__gmpz_and"
  | BOr -> "__gmpz_ior"
  | BXor -> "__gmpz_xor"
  | Shiftlt -> "__gmpz_mul_2exp"
  | Shiftrt -> "__gmpz_tdiv_q_2exp"
  | Lt | Gt | Le | Ge | Eq | Ne | LAnd | LOr | PlusPI | MinusPI
  | MinusPP as bop ->
    Options.fatal
      "Operation '%a' either not arithmetic or not supported on GMP integers"
      Printer.pp_binop bop

let init ~loc e = apply_on_var "init" ~loc e
let clear ~loc e = apply_on_var "clear" ~loc e

exception Longlong of ikind

let get_set_suffix_and_arg res_ty e =
  let ty = Cil.typeOf e in
  let exp_number_ty = Typing.number_ty_of_typ ~post:true ty in
  let res_number_ty = Typing.number_ty_of_typ ~post:true res_ty in
  let args_uisi e =
    if Gmp_types.Z.is_t res_ty then [ e ]
    else begin
      assert (Gmp_types.Q.is_t res_ty);
      [ e; Cil.one ~loc:e.eloc ]
    end
  in
  match (exp_number_ty, res_number_ty) with
  | Typing.Gmpz, Typing.Gmpz | Typing.Rational, Typing.Rational ->
    "", [ e ]
  | Typing.Gmpz, Typing.Rational ->
    "_z", [ e ]
  | Typing.Rational, Typing.Gmpz ->
    "_q", [ e ]
  | Typing.C_integer IChar, _ ->
    (if Cil.theMachine.Cil.theMachine.char_is_unsigned then "_ui"
     else "_si"),
    args_uisi e
  | Typing.C_integer (IBool | IUChar | IUInt | IUShort | IULong), _ ->
    "_ui", args_uisi e
  | Typing.C_integer (ISChar | IShort | IInt | ILong), _ ->
    "_si", args_uisi e
  | Typing.C_integer (ILongLong | IULongLong as ikind), _ ->
    raise (Longlong ikind)
  | Typing.C_float (FDouble | FFloat), _ ->
    (* FFloat is a strict subset of FDouble (modulo exceptional numbers)
       Hence, calling [set_d] for both of them is sound.
       HOWEVER: the machdep MUST NOT be vulnerable to double rounding
       [TODO] check the statement above *)
    "_d", [ e ]
  | Typing.C_float FLongDouble, _ ->
    Error.not_yet "creating gmp from long double"
  | Typing.Gmpz, _ | Typing.Rational, _ | Typing.Real, _ | Typing.Nan, _ -> (
      match Cil.unrollType ty with
      | TPtr(TInt(IChar, _), _) ->
        "_str",
        (* decimal base for the number given as string *)
        [ e; Cil.integer ~loc:e.eloc 10 ]
      | _ ->
        assert false
    )

let generic_affect ~loc fname lv ev e =
  let ty = Cil.typeOf ev in
  if Gmp_types.Z.is_t ty || Gmp_types.Q.is_t ty then begin
    let suf, args = get_set_suffix_and_arg ty e in
    Smart_stmt.rtl_call ~loc ~prefix:"" (fname ^ suf) (ev :: args)
  end else
    Smart_stmt.assigns ~loc:e.eloc ~result:lv e

let init_set ~loc lv ev e =
  let fname =
    let ty = Cil.typeOf ev in
    if Gmp_types.Z.is_t ty then
      "__gmpz_init_set"
    else if Gmp_types.Q.is_t ty then
      Options.fatal "no __gmpq_init_set: init then set separately"
    else
      ""
  in
  try generic_affect ~loc fname lv ev e
  with
  | Longlong IULongLong ->
    (match e.enode with
     | Lval elv ->
       assert (Gmp_types.Z.is_t (Cil.typeOf ev));
       let call =
         Smart_stmt.rtl_call ~loc
           ~prefix:""
           "__gmpz_import"
           [ ev;
             Cil.one ~loc;
             Cil.one ~loc;
             Cil.sizeOf ~loc (TInt(IULongLong, []));
             Cil.zero ~loc;
             Cil.zero ~loc;
             Cil.mkAddrOf ~loc elv ]
       in
       Smart_stmt.block_stmt (Cil.mkBlock [ init ~loc ev; call ])
     | _ ->
       Error.not_yet "unsigned long long expression requiring GMP")
  | Longlong ILongLong ->
    Error.not_yet "long long requiring GMP"

let affect ~loc lv ev e =
  let fname =
    let ty = Cil.typeOf ev in
    if Gmp_types.Z.is_t ty then "__gmpz_set"
    else if Gmp_types.Q.is_t ty then "__gmpq_set"
    else ""
  in
  try generic_affect ~loc fname lv ev e
  with Longlong _ ->
    Error.not_yet "quantification over long long and requiring GMP"

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
