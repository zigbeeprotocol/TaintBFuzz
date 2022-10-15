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

(** Manipulate the type of numbers. *)

type strnum =
  | Str_Z         (* integers *)
  | Str_R         (* reals *)
  | C_number      (* integers and floats included *)

let add_cast ~loc ?name env kf ctx strnum t_opt e =
  let mk_mpz e =
    let _, e, env =
      Env.new_var
        ~loc
        ?name
        env
        kf
        t_opt
        (Gmp_types.Z.t ())
        (fun lv v -> [ Gmp.init_set ~loc (Cil.var lv) v e ])
    in
    e, env
  in
  let e, env = match strnum with
    | Str_Z -> mk_mpz e
    | Str_R -> Rational.create ~loc ?name e env kf t_opt
    | C_number -> e, env
  in
  match ctx with
  | None ->
    e, env
  | Some ctx ->
    let ty = Cil.typeOf e in
    match Gmp_types.Z.is_t ty, Gmp_types.Z.is_t ctx with
    | true, true ->
      (* Z --> Z *)
      e, env
    | false, true ->
      if Gmp_types.Q.is_t ty then
        (* R --> Z *)
        Rational.cast_to_z ~loc ?name e env
      else
        (* C integer --> Z *)
        let e =
          if not (Cil.isIntegralType ty) && strnum = C_number then
            (* special case for \null that must be casted to long: it is the
               only non integral value that can be seen as an integer, while the
               type system infers that it is C-representable (see
               tests/runtime/null.i) *)
            Cil.mkCast ~newt:Cil.longType e (* \null *)
          else
            e
        in
        mk_mpz e
    | _, false ->
      if Gmp_types.Q.is_t ctx then
        if Gmp_types.Q.is_t (Cil.typeOf e) then (* R --> R *)
          e, env
        else (* C integer or Z --> R *)
          Rational.create ~loc ?name e env kf t_opt
      else if Gmp_types.Z.is_t ty || strnum = Str_Z then
        (* Z --> C type or the integer is represented by a string:
           anyway, it fits into a C integer: convert it *)
        let fname, new_ty =
          if Cil.isSignedInteger ctx then "__gmpz_get_si", Cil.longType
          else "__gmpz_get_ui", Cil.ulongType
        in
        let _, e, env =
          Env.new_var
            ~loc
            ?name
            env
            kf
            None
            new_ty
            (fun v _ ->
               [ Smart_stmt.rtl_call ~loc
                   ~result:(Cil.var v)
                   ~prefix:""
                   fname
                   [ e ] ])
        in
        e, env
      else if Gmp_types.Q.is_t ty || strnum = Str_R then
        (* R --> C type or the real is represented by a string *)
        Rational.add_cast ~loc ?name e env kf ctx
      else
        (* C type --> another C type *)
        Cil.mkCastT ~force:false ~oldt:ty ~newt:ctx e, env
