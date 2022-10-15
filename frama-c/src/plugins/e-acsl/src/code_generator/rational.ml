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

(* No init_set for GMPQ: init then set separately *)
let init_set ~loc lval vi_e e =
  Smart_stmt.block_stmt
    (Cil.mkBlock
       [ Gmp.init ~loc vi_e ;
         Gmp.affect ~loc lval vi_e e ])

let create ~loc ?name e env kf t_opt =
  let ty = Cil.typeOf e in
  if Gmp_types.Q.is_t ty then
    e, env
  else
    let _, e, env =
      Env.new_var
        ~loc
        ?name
        env
        kf
        t_opt
        (Gmp_types.Q.t ())
        (fun vi vi_e ->
           [ Gmp.init ~loc vi_e ;
             Gmp.affect ~loc (Cil.var vi) vi_e e ])
    in
    e, env

exception Not_a_decimal of string
exception Is_a_float

(* The possible float suffixes (ISO C 6.4.4.2) are lLfF.
   dD is a GNU extension accepted by Frama-C (only!) in the logic *)
let float_suffixes = [ 'f'; 'F'; 'l'; 'L'; 'd'; 'D' ]

(* Computes the fractional representation of a decimal number.
   Does NOT perform reduction.
   Example: [dec_to_frac "43.567"] evaluates to ["43567/1000"]
   Complexity: Linear
   Original Author: Frédéric Recoules

   It iterates **once** over [str] during which three cases are distinguished,
   example for "43.567":
   Case1: pre: no '.' has been found yet ==> copy current char into buf
    buf: | 4 |   |   |   |   |   |   |   |   |   |   |   |
         | 4 | 3 |   |   |   |   |   |   |   |   |   |   |
   Case2: mid: current char is '.' ==> put "/1" into buf at [(length str) - 1]
    buf: | 4 | 3 |   |   |   | / | 1 |   |   |   |   |   |
   Case3: post: a '.' was found ==> put current char in numerator AND '0' in den
    buf: | 4 | 3 | 5 |   |   | / | 1 | 0 |   |   |   |   |
         | 4 | 3 | 5 | 6 |   | / | 1 | 0 | 0 |   |   |   |
         | 4 | 3 | 5 | 6 | 7 | / | 1 | 0 | 0 | 0 |   |   | *)
let decimal_to_fractional str =
  let rec post str len buf len' i =
    if i = len then
      Bytes.sub_string buf 0 len'
    else
      match String.unsafe_get str i with
      | c when '0' <= c && c <= '9' ->
        Bytes.unsafe_set buf (i - 1) c;
        Bytes.unsafe_set buf len' '0';
        post str len buf (len' + 1) (i + 1)
      | c when List.mem c float_suffixes ->
        (* [JS] a suffix denoting a C type is possible *)
        assert (i = len - 1);
        raise Is_a_float
      | _ ->
        raise (Not_a_decimal str)
  in
  let mid buf len =
    Bytes.unsafe_set buf (len - 1) '/';
    Bytes.unsafe_set buf len '1'
  in
  let rec pre str len buf i =
    if i = len then
      str
    else
      match String.unsafe_get str i with
      | '.' ->
        mid buf len;
        post str len buf (len + 1) (i + 1)
      | c when '0' <= c && c <= '9' ->
        Bytes.unsafe_set buf i c;
        pre str len buf (i + 1)
      | c when List.mem c float_suffixes ->
        (* [JS] a suffix denoting a C type is possible *)
        assert (i = len - 1);
        raise Is_a_float
      | _ ->
        raise (Not_a_decimal str)
  in
  let strlen = String.length str in
  let buflen =
    (* The fractional representation is at most twice as lengthy
       as the decimal one. *)
    2 * strlen
  in
  try pre str strlen (Bytes.create buflen) 0
  with Is_a_float -> str (* just left it unchanged *)

(* ACSL considers strings written in decimal expansion to be reals.
   Yet GMPQ considers them to be double:
   they MUST be converted into fractional representation. *)
let normalize_str str =
  try
    decimal_to_fractional str
  with Invalid_argument _ ->
    Error.not_yet "number not written in decimal expansion"

let cast_to_z ~loc:_ ?name:_ e _env =
  assert (Gmp_types.Q.is_t (Cil.typeOf e));
  Error.not_yet "reals: cast from R to Z"

let add_cast ~loc ?name e env kf ty =
  (* TODO: The best solution would actually be to directly write all the needed
     functions as C builtins then just call them here depending on the situation
     at hand. *)
  assert (Gmp_types.Q.is_t (Cil.typeOf e));
  let get_double e env =
    let _, e, env =
      Env.new_var
        ~loc
        ?name
        env
        kf
        None
        Cil.doubleType
        (fun v _ ->
           [ Smart_stmt.rtl_call ~loc
               ~result:(Cil.var v)
               ~prefix:""
               "__gmpq_get_d"
               [ e ] ])
    in
    e, env
  in
  match Cil.unrollType ty with
  | TFloat(FLongDouble, _) ->
    (* The biggest floating-point type we can extract from GMPQ is double *)
    Error.not_yet "R to long double"
  | TFloat(FDouble, _) ->
    get_double e env
  | TFloat(FFloat, _) ->
    (* No "get_float" in GMPQ, but fortunately, [float] \subset [double].
       HOWEVER: going through double as intermediate step might be unsound since
       it could cause double rounding. See: [Boldo2013, Sec 2.2]
       https://hal.inria.fr/hal-00777639/document *)
    let e, env = get_double e env in
    Options.warning
      ~once:true "R to float: double rounding might cause unsoundness";
    Cil.mkCastT ~force:false ~oldt:Cil.doubleType ~newt:ty e, env
  | TInt(IULongLong, _) ->
    (* The biggest C integer type we can extract from GMP is ulong *)
    Error.not_yet "R to unsigned long long"
  | TInt _ ->
    (* 1) Cast R to Z using cast_to_z
       2) Extract ulong from Z
       3) Potentially cast ulong to ty *)
    Error.not_yet "R to Int"
  | _ ->
    Error.not_yet "R to <typ>"

let cmp ~loc bop e1 e2 env kf t_opt =
  let fname = "__gmpq_cmp" in
  let name = Misc.name_of_binop bop in
  (* TODO: [t1_opt] and [t2_opt] could be provided when creating [e1] and
     [e2] *)
  let e1, env = create ~loc e1 env kf None in
  let e2, env = create ~loc e2 env kf None in
  let _, e, env =
    Env.new_var
      ~loc
      env
      kf
      t_opt
      ~name
      Cil.intType
      (fun v _ ->
         [ Smart_stmt.rtl_call ~loc
             ~result:(Cil.var v)
             ~prefix:""
             fname
             [ e1; e2 ] ])
  in
  Cil.new_exp ~loc (BinOp(bop, e, Cil.zero ~loc, Cil.intType)), env

let new_var_and_init ~loc ?scope ?name env kf t_opt mk_stmts =
  Env.new_var
    ~loc
    ?scope
    ?name
    env
    kf
    t_opt
    (Gmp_types.Q.t ())
    (fun v e -> Gmp.init ~loc e :: mk_stmts v e)

let name_arith_bop = function
  | PlusA -> "__gmpq_add"
  | MinusA -> "__gmpq_sub"
  | Mult -> "__gmpq_mul"
  | Div -> "__gmpq_div"
  | Mod | Lt | Gt | Le | Ge | Eq | Ne | BAnd | BXor | BOr | LAnd | LOr
  | Shiftlt | Shiftrt | PlusPI | MinusPI | MinusPP -> assert false

let binop ~loc bop e1 e2 env kf t_opt =
  let name = name_arith_bop bop in
  (* TODO: [t1_opt] and [t2_opt] could be provided when creating [e1] and
     [e2] *)
  let e1, env = create ~loc e1 env kf None in
  let e2, env = create ~loc e2 env kf None in
  let mk_stmts _ e = [ Smart_stmt.rtl_call ~loc
                         ~prefix:""
                         name
                         [ e; e1; e2 ] ] in
  let name = Misc.name_of_binop bop in
  let _, e, env = new_var_and_init ~loc ~name env kf t_opt mk_stmts in
  e, env

(*
Local Variables:
compile-command: "make -C ../.."
End:
*)
