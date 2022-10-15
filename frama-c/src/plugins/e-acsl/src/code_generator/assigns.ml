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

exception NoAssigns

(*****************************************************************************)
(****************** Generation of function assigns ***************************)
(*****************************************************************************)

(* If an argument contains a pointer type, then it is undecidable which assigns
   clause should be generated, so skip the assigns generation in this case *)
let rec is_ptr_free typ = match Cil.unrollType typ with
  | TVoid _
  | TInt (_, _)
  | TFloat (_, _) -> true
  | TPtr (_, _) -> false
  | TArray (ty, _, _) -> is_ptr_free ty
  | TFun (_, _, _, _) ->
    (* a function cannot be an argument of a function *)
    assert false
  | TNamed (_, _) ->
    (* The named types are unfolded with [Cil.unrolltype] *)
    assert false
  | TEnum (_, _)
  | TBuiltin_va_list _ -> true
  | TComp (cinfo, _) ->
    match cinfo.cfields with
    | None -> raise NoAssigns
    | Some fields ->
      List.for_all
        (fun fi -> fi.fbitfield <> None || is_ptr_free fi.ftype)
        fields

(* For a GMP argument of a function, we generate an assigns from its address,
   since these are the only semantically valid operations on integers.
   For the argument [__e_acsl_mpz_struct * x], this function generates the
   expression [*(( __e_acsl_mpz_struct * )x)] *)
let deref_gmp_arg ~loc var =
  Smart_exp.lval ~loc
    (Mem (Cil.mkAddrOrStartOf ~loc (Var var , NoOffset)), NoOffset)

let rec get_assigns_from ~loc env lprofile lv =
  match lprofile with
  | [] -> []
  | lvar :: lvars ->
    let var = Env.Logic_binding.get env lvar  in
    if is_ptr_free var.vtype then
      Smart_exp.lval ~loc (Cil.var var) :: get_assigns_from ~loc env lvars lv
      (* If the argument contains a pointer, but is an integer, then it is
         necessarily a GMP type *)
    else if lvar.lv_type = Linteger then
      (deref_gmp_arg ~loc var) :: (get_assigns_from ~loc env lvars lv)
    else begin
      Options.warning ~current:true "skipping function %a when generating\
                                     assigns because pointers as arguments\
                                     is not yet supported"
        Printer.pp_logic_var lv;
      raise NoAssigns
    end

(* Special case when the function takes an extra argument as its result:
   For the argument [__e_acsl_mpz_t *__retres_arg], this function generates the
   expression [( *__retres_arg )[0]] *)
let get_gmp_integer ~loc vi =
  Smart_exp.lval
    ~loc
    (Mem
       (Smart_exp.lval  ~loc (Var vi, NoOffset)),
     (Index (Cil.zero ~loc, NoOffset)))
