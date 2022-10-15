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

(* Implement Figure 4 of J. Signoles' JFLA'15 paper "Rester statique pour
   devenir plus rapide, plus précis et plus mince". *)

let dkey = Options.Dkey.typing
module Error = Error.Make(struct let phase = dkey end)

(* In order to properly handle recursive functions the typing method has to
   store the result of the fixpoint algorithm on intervals before typing
   the inner block of the function. To this end, we stop the recursive
   depth-first descent of the AST at the level of function calls, and perform a
   breadth-first descent from the functions calls. We achieve this with
   a stack [pending_typing] which stores the roots of the functions calls from
   which a new descent is starting *)
let pending_typing : (unit -> unit) Stack.t = Stack.create ()

(******************************************************************************)
(** Datatype and constructor *)
(******************************************************************************)

type number_ty =
  | C_integer of ikind
  | C_float of fkind
  | Gmpz
  | Rational
  | Real
  | Nan

let ikind ik = C_integer ik
let c_int = ikind IInt
let gmpz = Gmpz
let fkind fk = C_float fk
let rational = Rational
let nan = Nan

module D =
  Datatype.Make_with_collections
    (struct
      type t = number_ty
      let name = "E_ACSL.Typing.t"
      let reprs = [ Gmpz; Real; Nan; c_int ]
      include Datatype.Undefined

      let compare ty1 ty2 =
        if ty1 == ty2 then 0
        else
          match ty1, ty2 with
          | C_integer i1, C_integer i2 ->
            if i1 = i2 then 0
            else if Cil.intTypeIncluded i1 i2 then -1 else 1
          | C_float f1, C_float f2 ->
            Stdlib.compare f1 f2
          | (C_integer _ | C_float _ | Gmpz | Rational | Real), Nan
          | (C_integer _ | C_float _ | Gmpz | Rational ), Real
          | (C_integer _ | C_float _ | Gmpz), Rational
          | (C_integer _ | C_float _), Gmpz
          | C_integer _, C_float _ ->
            -1
          | (C_float _ | Gmpz | Rational | Real | Nan), C_integer _
          | (Gmpz | Rational | Real | Nan), C_float _
          | (Rational | Real | Nan), Gmpz
          | (Real | Nan), Rational
          | Nan, Real ->
            1
          | Gmpz, Gmpz
          | Rational, Rational
          | Real, Real
          | Nan, Nan ->
            assert false

      let equal = Datatype.from_compare

      let hash = function
        | C_integer ik -> 7 * Hashtbl.hash ik
        | C_float fk -> 97 * Hashtbl.hash fk
        | Gmpz -> 787
        | Rational -> 907
        | Real -> 1011
        | Nan -> 1277

      let pretty fmt = function
        | C_integer k -> Printer.pp_ikind fmt k
        | C_float k -> Printer.pp_fkind fmt k
        | Gmpz -> Format.pp_print_string fmt "Gmpz"
        | Rational -> Format.pp_print_string fmt "Rational"
        | Real -> Format.pp_print_string fmt "Real"
        | Nan -> Format.pp_print_string fmt "Nan"
    end)

(******************************************************************************)
(** Basic operations *)
(******************************************************************************)

let join_cty ty1 ty2 =
  let ty = Cil.arithmeticConversion ty1 ty2 in
  match ty with
  | TInt(i, _) -> C_integer i
  | TFloat(f, _) -> C_float f
  | _ ->
    Options.fatal "[typing] join failure: unexpected result %a"
      Printer.pp_typ ty

let join ty1 ty2 =
  if ty1 == ty2 then ty1
  else
    match ty1, ty2 with
    | Nan, Nan | Real, Real | Rational, Rational | Gmpz, Gmpz ->
      assert false
    | Nan, (C_integer _ | C_float _ | Gmpz | Rational | Real as ty)
    | (C_integer _ | C_float _ | Gmpz | Rational | Real as ty), Nan ->
      Options.fatal "[typing] join failure: number %a and nan" D.pretty ty
    | Real, (C_integer _ | C_float _ | Gmpz | Rational)
    | (C_integer _ | C_float _ | Rational | Gmpz), Real ->
      Real
    | Rational, (C_integer _ | C_float _ | Gmpz)
    | (C_integer _ | C_float _ | Gmpz), Rational
    | C_float _, Gmpz
    | Gmpz, C_float _ ->
      Rational
    | Gmpz, C_integer _
    | C_integer _, Gmpz ->
      Gmpz
    | C_float f1, C_float f2 ->
      join_cty (TFloat(f1, [])) (TFloat(f2, []))
    | C_float f, C_integer n
    | C_integer n, C_float f ->
      join_cty (TFloat(f, [])) (TInt(n, []))
    | C_integer i1, C_integer i2 ->
      if Options.Gmp_only.get () then Gmpz
      else join_cty (TInt(i1, [])) (TInt(i2, []))

exception Not_a_number
let typ_of_number_ty = function
  | C_integer ik -> TInt(ik, [])
  | C_float fk -> TFloat(fk, [])
  | Gmpz -> Gmp_types.Z.t ()
  (* for the time being, no reals but rationals instead *)
  | Rational -> Gmp_types.Q.t ()
  | Real -> Error.not_yet "real number type"
  | Nan -> raise Not_a_number

let typ_of_lty = function
  | Ctype cty -> cty
  | Linteger -> Gmp_types.Z.t ()
  | Lreal -> Error.not_yet "real type"
  | Ltype _ | Lvar _ | Larrow _ -> Options.fatal "unexpected logic type"

(******************************************************************************)
(** Memoization *)
(******************************************************************************)

type computed_info =
  { ty: D.t;  (* type required for the term *)
    op: D.t; (* type required for the operation *)
    cast: D.t option; (* if not [None], type of the context which the term
                         must be casted to. If [None], no cast needed. *)
  }

(* Local environement = list of typed variables *)
module Function_params_ty =
  Datatype.List_with_collections
    (D)
    (struct let module_name = "E_ACSL.Typing.Function_params_ty" end)

module Id_term_with_lenv =
  Datatype.Pair_with_collections
    (Misc.Id_term)
    (Function_params_ty)
    (struct let module_name = "E_ACSL.Typing.Id_term_with_lenv" end)

(* Memoization module which retrieves the computed info of some terms. If the
   info is already computed for a term, it is never recomputed *)
module Memo: sig
  val memo:
    lenv:Function_params_ty.t ->
    (term -> computed_info) ->
    term ->
    computed_info Error.result
  val get: lenv:Function_params_ty.t -> term ->
    computed_info Error.result
  val clear: unit -> unit
end = struct

  (* The comparison over terms is the physical equality. It cannot be the
     structural one (given by [Cil_datatype.Term.equal]) because the very same
     term can be used in 2 different contexts which lead to different casts.

     By construction (see prepare_ast.ml), there are no physically equal terms
     in the E-ACSL's generated AST. Consequently the memoisation should be fully
     useless. However:
     - type info of many terms are accessed several times
     - the translation of E-ACSL guarded quantifications generates
       new terms (see module {!Quantif}) which must be typed. The term
       corresponding to the bound variable [x] is actually used twice: once in
       the guard and once for encoding [x+1] when incrementing it. The
       memoization is only useful here and indeed prevent the generation of one
       extra variable in some cases. *)
  let tbl : computed_info Error.result Misc.Id_term.Hashtbl.t =
    Misc.Id_term.Hashtbl.create 97

  (* The type of the logic function
     \\@ logic integer f (integer x) = x + 1;
     depends on the type of [x]. But our type system does not handle dependent
     types, which could let us express this dependency natively. Instead,
     we use the following trick to simulate the dependency: we type the
     corresponding definition (in the example [x+1]) several times,
     corresponding to the various calls to the function [f] in the program.
     We distinguish the calls to the function by storing the type of the
     arguments corresponding to each call, and we weaken the typing so that it
     is invariant when the arguments have the same type. *)
  let dep_tbl : computed_info Error.result Id_term_with_lenv.Hashtbl.t
    = Id_term_with_lenv.Hashtbl.create 97

  let get_dep lenv t =
    try Id_term_with_lenv.Hashtbl.find dep_tbl (t,lenv)
    with Not_found -> Error.not_memoized ()

  let get_nondep t =
    try Misc.Id_term.Hashtbl.find tbl t
    with Not_found -> Error.not_memoized ()

  let get ~lenv t =
    match lenv with
    | [] -> get_nondep t
    | _::_ -> get_dep lenv t

  let memo_nondep f t =
    try Misc.Id_term.Hashtbl.find tbl t
    with Not_found ->
      let x =
        try Result.Ok (f t)
        with Error.Not_yet _ | Error.Typing_error _ as exn -> Result.Error exn
      in
      Misc.Id_term.Hashtbl.add tbl t x;
      x

  let memo_dep f t lenv =
    try
      Id_term_with_lenv.Hashtbl.find dep_tbl (t, lenv)
    with Not_found ->
      let x =
        try Result.Ok (f t)
        with Error.Not_yet _ | Error.Typing_error _ as exn -> Result.Error exn
      in
      Id_term_with_lenv.Hashtbl.add dep_tbl (t, lenv) x;
      x

  let memo ~lenv f t =
    match lenv with
    | [] -> memo_nondep f t
    | _::_ -> memo_dep f t lenv

  let clear () =
    Options.feedback ~dkey ~level:4 "clearing the typing tables";
    Misc.Id_term.Hashtbl.clear tbl;
    Id_term_with_lenv.Hashtbl.clear dep_tbl

end

(******************************************************************************)
(** {2 Coercion rules} *)
(******************************************************************************)

(* Compute the smallest type (bigger than [int]) which can contain the whole
   interval. It is the \theta operator of the JFLA's paper. *)
let ty_of_interv ?ctx ?(use_gmp_opt = false) = function
  | Interval.Float(fk, _) -> C_float fk
  | Interval.Rational -> Rational
  | Interval.Real -> Real
  | Interval.Nan -> Nan
  | Interval.Ival iv ->
    try
      let kind = Interval.ikind_of_ival iv in
      (match ctx with
       | None
       | Some Nan ->
         C_integer kind
       | Some Gmpz ->
         if use_gmp_opt then Gmpz else C_integer kind
       | Some (C_integer ik as ctx) ->
         (* return [ctx] type for types smaller than int to prevent superfluous
            casts in the generated code *)
         if Cil.intTypeIncluded kind ik then ctx else C_integer kind
       | Some (C_float _ | Rational | Real as ty) ->
         ty)
    with Cil.Not_representable ->
    match ctx with
    | None | Some(C_integer _ | Gmpz | Nan) -> Gmpz
    | Some (C_float _ | Rational) -> Rational
    | Some Real -> Real

(* compute a new {!computed_info} by coercing the given type [ty] to the given
   context [ctx]. [op] is the type for the operator. *)
let coerce ~arith_operand ~ctx ~op ty =
  if D.compare ty ctx = 1 then
    (* type larger than the expected context,
       so we must introduce an explicit cast *)
    { ty; op; cast = Some ctx }
  else
    (* only add an explicit cast if the context is [Gmp] and [ty] is not;
       or if the term corresponding to [ty] is an operand of an arithmetic
       operation which must be explicitly coerced in order to force the
       operation to be of the expected type. *)
  if (ctx = Gmpz && ty <> Gmpz) || arith_operand
  then { ty; op; cast = Some ctx }
  else { ty; op; cast = None }

let number_ty_of_typ ~post ty =
  (* Consider GMP types only in a post typing phase *)
  if post && Gmp_types.Z.is_t ty then Gmpz
  else if post && Gmp_types.Q.is_t ty then Rational
  else
    match Cil.unrollType ty with
    | TInt(ik, _) | TEnum({ ekind = ik }, _) -> C_integer ik
    | TFloat(fk, _) -> C_float fk
    | TVoid _ | TPtr _ | TArray _ | TFun _ | TComp _ | TBuiltin_va_list _ -> Nan
    | TNamed _ -> assert false

let ty_of_logic_ty ?term lty =
  let get_ty = function
    | Linteger -> Gmpz
    | Ctype ty -> number_ty_of_typ ~post:false ty
    | Lreal -> Real
    | Larrow _ -> Nan
    | Ltype _ -> Error.not_yet "user-defined logic type"
    | Lvar _ -> Error.not_yet "type variable"
  in
  match term with
  | None -> get_ty lty
  | Some t ->
    if Options.Gmp_only.get () && lty = Linteger then Gmpz
    else
      let i = Interval.infer t in
      ty_of_interv i

(******************************************************************************)
(** {2 Type system} *)
(******************************************************************************)

(* generate a context [c]. Take --e-acsl-gmp-only into account iff [use_gmp_opt]
   is true. *)
let mk_ctx ~use_gmp_opt = function
  | C_float _ as f ->
    if use_gmp_opt && Options.Gmp_only.get () then Rational
    else f
  | C_integer _ as c ->
    if use_gmp_opt && Options.Gmp_only.get () then Gmpz
    else c
  | Gmpz | Rational | Real | Nan as c -> c

(* the number_ty corresponding to [t] whenever use as an offset.
   In that case, it cannot be a GMP, so it must be coerced to an integral type
   in that case *)
let type_offset t =
  let i = Interval.infer t in
  match ty_of_interv i with
  | Gmpz -> C_integer ILongLong (* largest possible type *)
  | ty -> ty

let type_letin li li_t =
  let i = Interval.infer li_t in
  Interval.Env.add li.l_var_info i

(* type the term [t] in a context [ctx] by taking --e-acsl-gmp-only into account
   iff [use_gmp_opt] is true. *)
let rec type_term
    ~use_gmp_opt
    ?(under_lambda=false)
    ?(arith_operand=false)
    ?ctx
    ~lenv
    t =
  let ctx = Option.map (mk_ctx ~use_gmp_opt) ctx in
  let dup ty = ty, ty in
  let compute_ctx ?ctx i =
    (* in order to get a minimal amount of generated casts for operators, the
       result is typed in the given context [ctx], but not the operands.
       This function returns a tuple (ctx_of_result, ctx_of_operands) *)
    match ctx with
    | None ->
      (* no context: factorize *)
      dup (mk_ctx ~use_gmp_opt:true (ty_of_interv i))
    | Some ctx ->
      mk_ctx ~use_gmp_opt:true (ty_of_interv ~ctx i),
      mk_ctx ~use_gmp_opt:true (ty_of_interv i)
  in
  let infer t =
    Cil.CurrentLoc.set t.term_loc;
    (* this pattern matching implements the formal rules of the JFLA's paper
       (and of course also covers the missing cases). Also enforce the invariant
       that every subterm is typed, even if it is not an integer. *)
    match t.term_node with
    | TConst (Integer _ | LChr _ | LEnum _ | LReal _)
    | TSizeOf _
    | TSizeOfStr _
    | TAlignOf _ ->
      let i = Interval.infer t in
      (* a constant or a left value directly under a lambda should be a gmp
         if the infered context for the lambda is gmp *)
      let ty = ty_of_interv ?ctx ~use_gmp_opt:under_lambda i in
      dup ty

    | TLval tlv ->
      let i = Interval.infer t in
      let ty =  ty_of_interv ?ctx ~use_gmp_opt:under_lambda i in
      type_term_lval ~lenv tlv;
      (* Options.feedback "Type : %a" D.pretty ty; *)
      dup ty

    | Toffset(_, t')
    | Tblock_length(_, t')
    | TSizeOfE t'
    | TAlignOfE t' ->
      let i = Interval.infer t in
      (* [t'] must be typed, but it is a pointer *)
      ignore (type_term ~use_gmp_opt:true ~ctx:Nan ~lenv t');
      let ty = ty_of_interv ?ctx i in
      dup ty

    | TBinOp (MinusPP, t1, t2) ->
      let i = Interval.infer t in
      (* [t1] and [t2] must be typed, but they are pointers *)
      ignore (type_term ~use_gmp_opt:true ~ctx:Nan ~lenv t1);
      ignore (type_term ~use_gmp_opt:true ~ctx:Nan ~lenv t2);
      let ty = ty_of_interv ?ctx i in
      dup ty

    | TUnOp (unop, t') ->
      let i = Interval.infer t in
      let i' = Interval.infer t' in
      let ctx_res, ctx = compute_ctx ?ctx (Interval.join i i') in
      ignore (type_term ~use_gmp_opt:true ~arith_operand:true ~ctx ~lenv t');
      (match unop with
       | LNot -> c_int, ctx_res (* converted into [t == 0] in case of GMP *)
       | Neg | BNot -> dup ctx_res)

    | TBinOp ((PlusA | MinusA | Mult | Div | Mod | Shiftlt | Shiftrt | BAnd
              | BOr | BXor), t1, t2)
      ->
      let i = Interval.infer t in
      let i1 = Interval.infer t1 in
      let i2 = Interval.infer t2 in
      let ctx_res, ctx =
        compute_ctx ?ctx (Interval.join i (Interval.join i1 i2))
      in
      (* it is enough to explicitly coerce when required one operand to [ctx]
         (through [arith_operand]) in order to force the type of the
         operation.  Heuristic: coerce the operand which is not a lval in
         order to lower the number of explicit casts *)
      let rec cast_first t1 t2 = match t1.term_node with
        | TLval _ -> false
        | TLogic_coerce(_, t) -> cast_first t t2
        | _ -> true
      in
      let cast_first = cast_first t1 t2 in
      ignore (type_term ~use_gmp_opt:true ~arith_operand:cast_first ~ctx ~lenv t1);
      ignore
        (type_term ~use_gmp_opt:true ~arith_operand:(not cast_first) ~ctx ~lenv t2);
      dup ctx_res

    | TBinOp ((Lt | Gt | Le | Ge | Eq | Ne), t1, t2) ->
      assert (match ctx with None -> true | Some c -> D.compare c c_int >= 0);
      let i1 = Interval.infer t1 in
      let i2 = Interval.infer t2 in
      let ctx =
        mk_ctx ~use_gmp_opt:true (ty_of_interv ?ctx (Interval.join i1 i2))
      in
      ignore (type_term ~use_gmp_opt:true ~ctx ~lenv t1);
      ignore (type_term ~use_gmp_opt:true ~ctx ~lenv t2);
      let ty = match ctx with
        | Nan -> c_int
        | Real | Rational | Gmpz | C_float _ | C_integer _ -> ctx
      in
      c_int, ty

    | TBinOp ((LAnd | LOr), t1, t2) ->
      let i1 = Interval.infer t1 in
      let i2 = Interval.infer t2 in
      let ty = ty_of_interv ?ctx (Interval.join i1 i2) in
      (* both operands fit in an int. *)
      ignore (type_term ~use_gmp_opt:true ~ctx:c_int ~lenv t1);
      ignore (type_term ~use_gmp_opt:true ~ctx:c_int ~lenv t2);
      dup ty

    | TCastE(_, t') ->
      (* compute the smallest interval from the whole term [t] *)
      let i = Interval.infer t in
      (* nothing more to do: [i] is already more precise than what we could
         infer from the arguments of the cast. *)
      let ctx = ty_of_interv ?ctx i in
      ignore (type_term ~use_gmp_opt:true ~ctx ~lenv t');
      dup ctx

    | Tif (t1, t2, t3) ->
      let ctx1 =
        mk_ctx ~use_gmp_opt:false c_int (* an int must be generated *)
      in
      ignore (type_term ~use_gmp_opt:false ~ctx:ctx1 ~lenv t1);
      let i = Interval.infer t in
      let i2 = Interval.infer t2 in
      let i3 = Interval.infer t3 in
      let ctx = ty_of_interv ?ctx (Interval.join i (Interval.join i2 i3)) in
      let ctx = mk_ctx ~use_gmp_opt:true ctx in
      ignore (type_term ~use_gmp_opt:true ~ctx ~lenv t2);
      ignore (type_term ~use_gmp_opt:true ~ctx ~lenv t3);
      dup ctx

    | Tat (t, _)
    | TLogic_coerce (_, t) ->
      dup (type_term ~use_gmp_opt ~arith_operand ?ctx ~lenv t).ty

    | TAddrOf tlv
    | TStartOf tlv ->
      (* it is a pointer, but subterms must be typed. *)
      type_term_lval tlv ~lenv;
      dup Nan

    | Tbase_addr (_, t) ->
      (* it is a pointer, but subterms must be typed. *)
      ignore (type_term ~use_gmp_opt:true ~ctx:Nan ~lenv t);
      dup Nan

    | TBinOp ((PlusPI | MinusPI), t1, t2) ->
      (* both [t1] and [t2] must be typed. *)
      ignore (type_term ~use_gmp_opt:true ~ctx:Nan ~lenv t1);
      let ctx = type_offset t2 in
      ignore (type_term ~use_gmp_opt:false ~ctx ~lenv t2);
      dup Nan

    | Tapp(li, _, args) ->
      if Builtins.mem li.l_var_info.lv_name then
        let typ_arg lvi arg =
          (* a built-in is a C function, so the context is necessarily a C
             type. *)
          let ctx = ty_of_logic_ty lvi.lv_type in
          ignore (type_term ~use_gmp_opt:false ~ctx ~lenv arg)
        in
        List.iter2 typ_arg li.l_profile args;
        (* [li.l_type is [None] for predicate only: not possible here.
           Thus using [Option.get] is fine *)
        dup (ty_of_logic_ty (Option.get li.l_type))
      else begin
        (* TODO: what if the type of the parameter is smaller than the infered
           type of the argument? For now, it is silently ignored (both
           statically and at runtime)... *)
        (* TODO: recursive call in arguments of function call *)
        match li.l_body with
        | LBpred p ->
          (* possible to have an [LBpred] here because we transformed
             [Papp] into [Tapp] *)
          Stack.push
            (fun () ->
               let typed_args =
                 type_args
                   ~use_gmp_opt
                   ~lenv
                   li.l_profile
                   args
                   li.l_var_info.lv_name
               in
               ignore (type_predicate ~lenv:typed_args p);
               List.iter Interval.Env.remove li.l_profile)
            pending_typing;
          dup c_int
        | LBterm t_body ->
          begin match li.l_type with
            | None ->
              assert false
            | Some lty ->
              (* TODO: what if the function returns a real? *)
              let ty = ty_of_logic_ty ~term:t lty in
              let type_args_and_body () =
                let typed_args =
                  type_args
                    ~use_gmp_opt
                    ~lenv
                    li.l_profile
                    args
                    li.l_var_info.lv_name
                in
                (* Since there are no global logic variables, the typing of the
                   inner block of the function only depends on the function's
                   own arguments, so the [~lenv] parameter gets replaced with
                   the type of the parameters in the current function calls *)
                ignore (type_term ~use_gmp_opt ~lenv:typed_args t_body)
              in
              let clear_env () = List.iter Interval.Env.remove li.l_profile in
              Stack.push
                clear_env
                pending_typing;
              Stack.push
                type_args_and_body
                pending_typing;
              dup ty
          end
        | LBnone ->
          (match args with
           | [ t1; t2; {term_node = Tlambda([ _ ], _)} as lambda ] ->
             let anonymous =
               Logic_const.term (TBinOp(PlusA, t2, Cil.lone ())) Linteger
             in
             let ty_bound = Interval.infer anonymous in
             let ty_bound =
               ty_of_interv (Interval.join ty_bound (Interval.infer t1))
             in
             ignore
               (type_term
                  ~use_gmp_opt:true ~arith_operand:true ~ctx:ty_bound ~lenv t1);
             ignore
               (type_term
                  ~use_gmp_opt:true ~arith_operand:true ~ctx:ty_bound ~lenv t2);
             let ty = ty_of_interv (Interval.infer t) ~use_gmp_opt:true ?ctx in
             (* Options.feedback "type of extended quantifier: %a" D.pretty ty; *)
             ignore (type_term ~use_gmp_opt:true ?ctx ~lenv lambda);
             dup ty
           | [ ] | [ _ ] | [ _; _ ] | _ :: _ :: _ :: _ ->
             (* TODO : improve error message to distinguish error messages
                corresponding to unsupported primitives and wrong application
                of supported primitive
                (one is a fatal and the other is a not_yet) *)
             Error.not_yet "logic functions or predicates with no definition \
                            nor reads clause")
        | LBreads _ ->
          Error.not_yet "logic functions or predicates performing read accesses"
        | LBinductive _ ->
          Error.not_yet "inductive logic functions"
      end

    | Tunion _ -> Error.not_yet "tset union"
    | Tinter _ -> Error.not_yet "tset intersection"
    | Tcomprehension (_,_,_) -> Error.not_yet "tset comprehension"

    | Trange(None, _) | Trange(_, None) ->
      Options.abort "unbounded ranges are not part of E-ACSl"
    | Trange(Some n1, Some n2) ->
      ignore (type_term ~use_gmp_opt ~lenv n1);
      ignore (type_term ~use_gmp_opt ~lenv n2);
      let i = Interval.infer t in
      let ty = ty_of_interv ?ctx i in
      dup ty

    | Tlet(li, t) ->
      let li_t = Misc.term_of_li li in
      type_letin li li_t;
      ignore (type_term ~use_gmp_opt:true ~lenv li_t);
      dup (type_term ~use_gmp_opt:true ?ctx ~lenv t).ty
    | Tlambda ([ _ ],lt) ->
      dup (type_term ~use_gmp_opt:true ~under_lambda:true ?ctx ~lenv lt).ty;
    | Tlambda (_,_) -> Error.not_yet "lambda"
    | TDataCons (_,_) -> Error.not_yet "datacons"
    | TUpdate (_,_,_) -> Error.not_yet "update"

    | Tnull
    | TConst (LStr _ | LWStr _)
    | Ttypeof _
    | Ttype _
    | Tempty_set  -> dup Nan
  in
  let t = Logic_normalizer.get_term t in
  match
    Memo.memo ~lenv
      (fun t ->
         let ty, op = infer t in
         match ctx with
         | None -> { ty; op; cast = None }
         | Some ctx -> coerce ~arith_operand ~ctx ~op ty)
      t
  with
  | Result.Ok res -> res
  | Result.Error exn -> raise exn

and type_term_lval ~lenv (host, offset) =
  type_term_lhost ~lenv host;
  type_term_offset ~lenv offset

and type_term_lhost ~lenv t  = match t with
  | TVar _
  | TResult _ -> ()
  | TMem t -> ignore (type_term ~use_gmp_opt:false ~ctx:Nan ~lenv t)

and type_term_offset ~lenv t = match t with
  | TNoOffset -> ()
  | TField(_, toff)
  | TModel(_, toff) -> type_term_offset ~lenv toff
  | TIndex(t, toff) ->
    let ctx = type_offset t in
    ignore (type_term ~use_gmp_opt:false ~ctx ~lenv t);
    type_term_offset ~lenv toff

and type_args params ~use_gmp_opt ~lenv args fname =
  try
    List.fold_right2
      (fun lv t (typed_args : Function_params_ty.t) ->
         let ty_arg = (type_term ~use_gmp_opt ~lenv t).ty in
         begin
           try
             let typ_arg = typ_of_number_ty ty_arg in
             Interval.Env.add lv (Interval.interv_of_typ typ_arg)
           with Not_a_number -> ()
         end;
         ty_arg :: typed_args)
      params
      args
      []
  with Invalid_argument _ ->
    Options.fatal "[Tapp] unexpected number of arguments when calling %s" fname

(* [type_bound_variables] infers an interval associated with each of
   the provided bounds of a quantified variable, and provides a term
   accordingly. It could happen that the bounds provided for a quantifier
   [lv] are bigger than its type. [type_bound_variables] handles such cases
   and provides smaller bounds whenever possible.
   Let B be the inferred interval and R the range of [lv.typ]
   - Case 1: B \subseteq R
     Example: [\forall unsigned char c; 4 <= c <= 100 ==> 0 <= c <= 255]
     Return: B
   - Case 2: B \not\subseteq R and the bounds of B are inferred exactly
     Example: [\forall unsigned char c; 4 <= c <= 300 ==> 0 <= c <= 255]
     Return: B \intersect R
   - Case 3: B \not\subseteq R and the bounds of B are NOT inferred exactly
     Example: [\let m = n > 0 ? 4 : 341; \forall char u; 1 < u < m ==> u > 0]
     Return: R with a guard guaranteeing that [lv] does not overflow *)
and type_bound_variables ~loc ~lenv (t1, lv, t2) =
  let i1 = Interval.infer t1 in
  let i2 = Interval.infer t2 in
  let i = Interval.(widen (join i1 i2)) in
  let ctx = match lv.lv_type with
    | Linteger -> mk_ctx ~use_gmp_opt:true (ty_of_interv ~ctx:Gmpz i)
    | Ctype ty ->
      (match Cil.unrollType ty with
       | TInt(ik, _) -> mk_ctx ~use_gmp_opt:true (C_integer ik)
       | ty ->
         Options.fatal "unexpected C type %a for quantified variable %a"
           Printer.pp_typ ty
           Printer.pp_logic_var lv)
    | lty ->
      Options.fatal "unexpected logic type %a for quantified variable %a"
        Printer.pp_logic_type lty
        Printer.pp_logic_var lv
  in
  let t1, t2, i =
    match lv.lv_type with
    | Ltype _ | Lvar _ | Lreal | Larrow _ ->
      Error.not_yet "quantification over non-integer type"
    | Linteger -> t1, t2, i
    | Ctype ty ->
      let ity = Interval.extended_interv_of_typ ty in
      if Interval.is_included i ity then
        (* case 1 *)
        t1, t2, i
      else if Interval.is_singleton_int i1 &&
              Interval.is_singleton_int i2 then
        begin
          (* case 2 *)
          let i = Interval.meet i ity in
          (* We can now update the bounds in the preprocessed form
             that come from the meet of the two intervals *)
          let min, max = Misc.finite_min_and_max (Interval.extract_ival i) in
          let t1 = Logic_const.tint ~loc min in
          let t2 = Logic_const.tint ~loc max in
          t1, t2, i
        end else
        (* case 3 *)
        let min, max = Misc.finite_min_and_max (Interval.extract_ival ity) in
        let guard_lower = Logic_const.tint ~loc min in
        let guard_upper = Logic_const.tint ~loc max in
        let lv_term = Logic_const.tvar ~loc lv in
        let guard_lower = Logic_const.prel ~loc (Rle, guard_lower, lv_term) in
        let guard_upper = Logic_const.prel ~loc (Rlt, lv_term, guard_upper) in
        let guard = Logic_const.pand ~loc (guard_lower, guard_upper) in
        ignore (type_predicate ~lenv guard);
        Bound_variables.add_guard_for_small_type lv guard;
        t1, t2, i
  in
  (* forcing when typing bounds prevents to generate an extra useless
     GMP variable when --e-acsl-gmp-only *)
  ignore (type_term ~use_gmp_opt:false ~ctx ~lenv t1);
  ignore (type_term ~use_gmp_opt:false ~ctx ~lenv t2);
  (* if we must generate GMP code, degrade the interval in order to
     guarantee that [x] will be a GMP when typing the goal *)
  let i = match ctx with
    | C_integer _ -> i
    (* [ -\infty; +\infty ] *)
    | Gmpz -> Interval.Ival (Ival.inject_range None None)
    | C_float _ | Rational | Real | Nan ->
      Options.fatal "unexpected quantification over %a" D.pretty ctx
  in
  Interval.Env.add lv i;
  (t1, lv, t2)

and type_predicate ~lenv p =
  let p = Logic_normalizer.get_pred p in
  Cil.CurrentLoc.set p.pred_loc;
  (* this pattern matching also follows the formal rules of the JFLA's paper *)
  let op =
    match p.pred_content with
    | Pfalse | Ptrue -> c_int
    | Papp(li, _, args) ->
      begin
        match li.l_body with
        | LBpred p ->
          let typed_args =
            type_args
              ~use_gmp_opt:true
              ~lenv
              li.l_profile
              args
              li.l_var_info.lv_name
          in
          ignore (type_predicate ~lenv:typed_args p);
          List.iter Interval.Env.remove li.l_profile
        | LBnone -> ()
        | LBreads _ -> ()
        | LBinductive _ -> ()
        | LBterm _ ->
          Options.fatal "unexpected logic definition"
            Printer.pp_predicate p
      end;
      c_int
    | Pdangling _ -> Error.not_yet "\\dangling"
    | Prel(_, t1, t2) ->
      let i1 = Interval.infer t1 in
      let i2 = Interval.infer t2 in
      let i = Interval.join i1 i2 in
      let ctx = mk_ctx ~use_gmp_opt:true (ty_of_interv ~ctx:c_int i) in
      ignore (type_term ~use_gmp_opt:true ~ctx ~lenv t1);
      ignore (type_term ~use_gmp_opt:true ~ctx ~lenv t2);
      (match ctx with
       | Nan -> c_int
       | Real | Rational | Gmpz | C_float _ | C_integer _ -> ctx)
    | Pand(p1, p2)
    | Por(p1, p2)
    | Pxor(p1, p2)
    | Pimplies(p1, p2)
    | Piff(p1, p2) ->
      ignore (type_predicate ~lenv p1);
      ignore (type_predicate ~lenv p2);
      c_int
    | Pnot p ->
      ignore (type_predicate ~lenv p);
      c_int
    | Pif(t, p1, p2) ->
      let ctx = mk_ctx ~use_gmp_opt:false c_int in
      ignore (type_term ~use_gmp_opt:false ~ctx ~lenv t);
      ignore (type_predicate ~lenv p1);
      ignore (type_predicate ~lenv p2);
      c_int
    | Plet(li, p) ->
      let li_t = Misc.term_of_li li in
      type_letin li li_t;
      ignore (type_term ~use_gmp_opt:true ~lenv li_t);
      (type_predicate ~lenv p).ty
    | Pforall _
    | Pexists _ ->
      begin
        let guards, goal =
          Error.retrieve_preprocessing
            "preprocessing of quantified predicate"
            Bound_variables.get_preprocessed_quantifier
            p
            Printer.pp_predicate
        in
        let guards =
          List.map
            (fun (t1, x, t2) ->
               type_bound_variables ~loc:p.pred_loc ~lenv (t1, x, t2))
            guards
        in Bound_variables.replace p guards goal;
        (type_predicate ~lenv goal).ty
      end
    | Pseparated tlist ->
      List.iter
        (fun t ->
           ignore
             (type_term ~use_gmp_opt:false ~ctx:Nan ~lenv t))
        tlist;
      c_int
    | Pinitialized(_, t)
    | Pfreeable(_, t)
    | Pallocable(_, t)
    | Pvalid(_, t)
    | Pvalid_read(_, t)
    | Pobject_pointer(_,t)
    | Pvalid_function t ->
      ignore (type_term ~use_gmp_opt:false ~ctx:Nan ~lenv t);
      c_int
    | Pat(p, _) -> (type_predicate ~lenv p).ty
    | Pfresh _ -> Error.not_yet "\\fresh"
  in
  coerce ~arith_operand:false ~ctx:c_int ~op c_int

let type_term ~use_gmp_opt ?ctx ~lenv t =
  Options.feedback ~dkey ~level:4 "typing term '%a' in ctx '%a'."
    Printer.pp_term t (Pretty_utils.pp_opt D.pretty) ctx;
  ignore (type_term ~use_gmp_opt ?ctx ~lenv t);
  while not (Stack.is_empty pending_typing) do
    Stack.pop pending_typing ()
  done

let type_named_predicate ~lenv p =
  Options.feedback ~dkey ~level:3 "typing predicate '%a'."
    Printer.pp_predicate p;
  ignore (type_predicate ~lenv p);
  while not (Stack.is_empty pending_typing) do
    Stack.pop pending_typing ()
  done

let unsafe_set t ?ctx ~lenv ty =
  let ctx = match ctx with None -> ty | Some ctx -> ctx in
  let mk _ = coerce ~arith_operand:false ~ctx ~op:ty ty in
  ignore (Memo.memo mk ~lenv t)

(******************************************************************************)
(** {2 Getters} *)
(******************************************************************************)

let get_number_ty ~lenv t =
  (Error.retrieve_preprocessing "typing" (Memo.get ~lenv) t Printer.pp_term).ty
let get_integer_op ~lenv t =
  (Error.retrieve_preprocessing "typing" (Memo.get ~lenv) t Printer.pp_term).op
let get_integer_op_of_predicate ~lenv p = (type_predicate ~lenv p).op

(* {!typ_of_integer}, but handle the not-integer cases. *)
let extract_typ t ty =
  try typ_of_number_ty ty
  with Not_a_number ->
  match t.term_type with
  | Ctype _ as lty -> Logic_utils.logicCType lty
  | Linteger | Lreal ->
    Options.fatal "unexpected context NaN for term %a" Printer.pp_term t
  | Ltype _ -> Error.not_yet "unsupported logic type: user-defined type"
  | Lvar _ -> Error.not_yet "unsupported logic type: type variable"
  | Larrow _ -> Error.not_yet "unsupported logic type: type arrow"

let get_typ ~lenv t =
  let info =
    Error.retrieve_preprocessing "typing" (Memo.get ~lenv) t Printer.pp_term in
  extract_typ t info.ty

let get_op ~lenv t =
  let info =
    Error.retrieve_preprocessing "typing" (Memo.get ~lenv) t Printer.pp_term  in
  extract_typ t info.op

let get_cast ~lenv t =
  let info =
    Error.retrieve_preprocessing "typing" (Memo.get ~lenv) t Printer.pp_term in
  try Option.map typ_of_number_ty info.cast
  with Not_a_number -> None

let get_cast_of_predicate ~lenv p =
  let info = type_predicate ~lenv p in
  try Option.map typ_of_number_ty info.cast
  with Not_a_number -> assert false

let clear = Memo.clear

let typing_visitor lenv = object
  inherit E_acsl_visitor.visitor dkey

  (* global logic functions and predicates are evaluated are callsites *)
  method !glob_annot _ = Cil.SkipChildren

  method !vpredicate p =
    (* Do not raise a warning for e-acsl errors at preprocessing time,
       those errrors are stored in the table and warnings are raised at
       translation time *)
    ignore
      (try type_named_predicate ~lenv p
       with Error.Not_yet _ | Error.Typing_error _  -> ());
    Cil.SkipChildren
end

let type_program ast =
  let visitor = typing_visitor [] in
  visitor#visit_file ast

let type_code_annot lenv annot =
  let visitor = typing_visitor lenv in
  ignore @@ visitor#visit_code_annot annot

let preprocess_predicate lenv p =
  Logic_normalizer.preprocess_predicate p;
  Bound_variables.preprocess_predicate p;
  let visitor = typing_visitor lenv in
  ignore @@ visitor#visit_predicate p

let preprocess_rte ~lenv rte =
  Logic_normalizer.preprocess_annot rte;
  Bound_variables.preprocess_annot rte;
  type_code_annot lenv rte

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
