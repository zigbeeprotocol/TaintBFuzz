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
(********************** Forward references ********************************)
(**************************************************************************)

let predicate_to_exp_ref
  : (adata:Assert.t ->
     kernel_function ->
     Env.t ->
     predicate ->
     exp * Assert.t * Env.t) ref
  =
  ref (fun ~adata:_ _kf _env _p ->
      Extlib.mk_labeled_fun "predicate_to_exp_ref")

let term_to_exp_ref
  : (adata:Assert.t ->
     kernel_function ->
     Env.t ->
     term ->
     exp * Assert.t * Env.t) ref
  =
  ref (fun ~adata:_ _kf _env _t -> Extlib.mk_labeled_fun "term_to_exp_ref")

let gmp_to_sizet_ref
  : (adata:Assert.t ->
     loc:location ->
     name:string ->
     ?check_lower_bound:bool ->
     ?pp:term ->
     kernel_function ->
     Env.t ->
     term ->
     exp * Assert.t * Env.t) ref
  =
  let func ~adata:_ ~loc:_ ~name:_ ?check_lower_bound:_ ?pp:_ _kf _env _t =
    Extlib.mk_labeled_fun "gmp_to_sizet_ref"
  in
  ref func

(*****************************************************************************)
(****************************** Ranges Elimination ***************************)
(*****************************************************************************)

(* We call Range Elimination the operation through which ranges are
   substituted by universally quantified logic variables.
   Example:
    [\valid(&t[(n-1)..(n+2)][1][0..1])] can be soundly transformed into
    [\forall integer q1; n-1 <= q1 <= n+2 ==>
      \forall integer q2; 0 <= q2 <= 1 ==>
        \valid(&t[q1][1][q2])]
   However, the substitution can be unsound,
   in which case [Range_elimination_exception] must be raised.
   Example:
    [\valid(&t[(0..2)==(0..2) ? 0 : 1])] is equivalent to [\valid(&t[0])]
      since [==] refers to set equality when applied on ranges.
    But Range Elimination will give a predicate equivalent to [\valid(&t[1])]
      since [\forall 0 <= q1,q2 <= 2: q1==q2] is false.
    Hence [Range_elimination_exception] must be raised. *)
exception Range_elimination_exception

(* Take a [toffset] and check whether it contains an index that is a set *)
let rec has_set_as_index = function
  | TNoOffset ->
    false
  | TIndex(t, toffset) ->
    Logic_const.is_set_type t.term_type || has_set_as_index toffset
  | TModel(_, toffset) | TField(_, toffset) ->
    has_set_as_index toffset

(* Perform Range Elimination on index [TIndex(term, offset)]. Term part.
   Raise [Range_elimination_exception] whether either the operation is unsound
   or we don't support the construction yet. *)
let eliminate_ranges_from_index_of_term ~loc t =
  match t.term_node with
  | Trange(Some n1, Some n2) ->
    let name = Varname.get ~scope:Varname.Block "range" in
    let lv = Cil_const.make_logic_var_kind name LVQuant Linteger in
    let tlv = Logic_const.tvar ~loc lv in
    tlv, (n1, lv, n2)
  | _ ->
    raise Range_elimination_exception

(* Perform Range Elimination on index [TIndex(term, offset)]. Offset part.
   Raise [Range_elimination_exception], through [eliminate_ranges_from_
   index_of_term], whether either the operation is unsound or we don't support
   the construction yet. *)
let rec eliminate_ranges_from_index_of_toffset ~loc toffset quantifiers =
  match toffset with
  | TIndex(t, toffset') ->
    if Misc.is_range_free t then
      let toffset', quantifiers' =
        eliminate_ranges_from_index_of_toffset ~loc toffset' quantifiers
      in
      TIndex(t, toffset'), quantifiers'
    else
      (* Attempt Range Elimination on [t] *)
      let t1, quantifiers1 =
        eliminate_ranges_from_index_of_term ~loc t
      in
      let toffset2, quantifiers2 =
        eliminate_ranges_from_index_of_toffset ~loc toffset' quantifiers
      in
      let toffset3 = TIndex(t1, toffset2) in
      toffset3, quantifiers1 :: quantifiers2
  | TNoOffset ->
    toffset, quantifiers
  | TModel _ ->
    Error.not_yet "range elimination on TModel"
  | TField _ ->
    Error.not_yet "range elimination on TField"

(*****************************************************************************)
(********************** Calls without Range Elimination **********************)
(************** \base_addr, \block_length, \offset, \freeable ****************)
(*****************************************************************************)

(* \base_addr, \block_length, \offset and \freeable *)
let call ~adata ~loc kf name ctx env t =
  assert (name = "base_addr" || name = "block_length"
          || name = "offset" || name ="freeable");
  let (e, adata), env =
    Env.with_params_and_result
      ~rte:true
      ~f:(fun env ->
          let e, adata, env = !term_to_exp_ref ~adata kf env t in
          (e, adata), env)
      env
  in
  let e, env =
    Env.rtl_call_to_new_var
      ~loc
      ~name
      env
      kf
      None
      ctx
      name
      [ e ]
  in
  e, adata, env

(*****************************************************************************)
(************************* Calls with Range Elimination **********************)
(********************** \initialized, \valid, \valid_read ********************)
(*****************************************************************************)

(* Take the term [size] that has been typed into GMP
   and return an expression of type [size_t].
   The case where [!(0 <= size <= SIZE_MAX)] is an UB ==> guard against it.
   Since the case [0 <= size] is already checked before calling this function,
   only [size <= SIZE_MAX] is added as a guard. *)
let gmp_to_sizet ~adata ~loc ?pp kf env size _p =
  !gmp_to_sizet_ref
    ~adata
    ~loc
    ~name:"offset"
    ~check_lower_bound:false
    ?pp
    kf
    env
    size

(* Take a term of the form [ptr + r] where [ptr] is an address and [r] a range
   offset, and return a tuple [(ptr, size, env)] where [ptr] is the address of
   the start of the range, [size] is the size of the range in bytes and [env] is
   the current environment.
   [p] is the predicate under test. *)
let range_to_ptr_and_size ~adata ~loc kf env ptr r p =
  let n1, n2 = match r.term_node with
    | Trange(Some n1, Some n2) ->
      n1, n2
    | Trange(None, _) | Trange(_, None) ->
      Options.abort "unbounded ranges are not part of E-ACSL"
    | _ ->
      assert false
  in
  (* s *)
  let ty = match Cil.unrollType (Misc.cty ptr.term_type) with
    | TPtr(ty, _) | TArray(ty, _, _) -> ty
    | _ -> assert false
  in
  let s = Logic_const.term ~loc (TSizeOf ty) Linteger in
  (* ptr *)
  let typ_charptr = Cil.charPtrType in
  let ptr = Logic_const.term
      ~loc
      (TBinOp(
          PlusPI,
          Logic_utils.mk_cast ~loc ~force:false typ_charptr ptr,
          Logic_const.term ~loc (TBinOp(Mult, s, n1)) Linteger))
      (Ctype typ_charptr)
  in
  Typing.type_term
    ~use_gmp_opt:false
    ~ctx:Typing.nan
    ~lenv:(Env.Local_vars.get env)
    ptr;
  let (ptr, adata), env =
    Env.with_params_and_result
      ~rte:true
      ~f:(fun env ->
          let e, adata, env = !term_to_exp_ref ~adata kf env ptr in
          (e, adata), env)
      env
  in
  (* size *)
  let size_term =
    (* Since [s] and [n1] have been typed through [ptr],
       we need to clone them in order to force retyping *)
    let s = { s with term_node = s.term_node } in
    let n1 = { n1 with term_node = n1.term_node } in
    (* The range are inclusives, so the total number of elements is
       [n2 - n1 + 1] *)
    let count = Logic_const.term
        ~loc
        (TBinOp (
            PlusA,
            Logic_const.term ~loc (TBinOp (MinusA, n2, n1)) Linteger,
            Logic_const.tinteger ~loc 1))
        Linteger
    in
    let size_term = Logic_const.term ~loc (TBinOp (Mult, s, count)) Linteger in
    (* Create a let binding with the value of the size *)
    let size_term_info =
      { l_var_info = Cil_const.make_logic_var_local "size" Linteger;
        l_type = None;
        l_tparams = [];
        l_labels = [];
        l_profile = [];
        l_body = LBterm size_term;
      }
    in
    let size_term_lv = Logic_const.tvar ~loc size_term_info.l_var_info in
    (* If [size_term <= 0], then the range represents an empty set and the size
       should be set to exactly [0]. *)
    let tzero = Logic_const.tinteger ~loc 0 in
    let size_term_if =
      Logic_const.term
        ~loc
        (Tif (Logic_const.term ~loc (TBinOp (Le, size_term_lv, tzero)) Linteger,
              tzero,
              size_term_lv))
        Linteger
    in
    Logic_const.term ~loc (Tlet (size_term_info, size_term_if)) Linteger
  in
  let lenv = Env.Local_vars.get env in
  Typing.type_term ~use_gmp_opt:false ~lenv size_term;
  let size, adata, env =
    match Typing.get_number_ty size_term  ~lenv with
    | Typing.Gmpz ->
      (* Start by translating [size_term] to an expression so that the full term
         with [\let] is not passed around. *)
      let size_e, adata, env = !term_to_exp_ref ~adata kf env size_term in
      (* Since translating a GMP code should always produce a C variable, we
         can reuse it as a term for the function [gmp_to_sizet]. *)
      let cvar_term =
        match size_e.enode with
        | Lval (Var vi, NoOffset) -> Cil.cvar_to_term ~loc vi
        | _ ->
          Options.fatal
            "translation to GMP code should always return a C variable"
      in
      gmp_to_sizet ~adata ~loc ~pp:size_term kf env cvar_term p
    | Typing.(C_integer _ | C_float _) ->
      !term_to_exp_ref ~adata kf env size_term
    | Typing.(Rational | Real | Nan) ->
      assert false
  in
  ptr, size, adata, env

(* Take a term without range [t] and return a tuple [(ptr, size, env)] where
   [ptr] is an expression representing the term, [size] is the size of the
   expression in bytes and [env] is the current environment.
   [p] is the predicate under test. *)
let term_to_ptr_and_size ~adata ~loc kf env t =
  let (e, adata), env =
    Env.with_params_and_result
      ~rte:true
      ~f:(fun env ->
          let e, adata, env = !term_to_exp_ref ~adata kf env t in
          (e, adata), env)
      env
  in
  let ty = Misc.cty t.term_type in
  let sizeof = Smart_exp.ptr_sizeof ~loc ty in
  let adata, env =
    Assert.register
      ~loc:t.term_loc
      env
      (Format.asprintf "%a" Printer.pp_exp sizeof)
      sizeof
      adata
  in
  e, sizeof, adata, env

(* [fname_to_pred name args] returns the memory predicate corresponding to
   [name] with the given [args]. *)
let fname_to_pred ?loc name args =
  match name, args with
  | "dangling", [ t ] ->
    Logic_const.pdangling ?loc (Logic_const.here_label, t)
  | "valid", [ t ] ->
    Logic_const.pvalid ?loc (Logic_const.here_label, t)
  | "valid_read", [ t ] ->
    Logic_const.pvalid_read ?loc (Logic_const.here_label, t)
  | "separated", args ->
    Logic_const.pseparated ?loc args
  | "initialized", [ t ] ->
    Logic_const.pinitialized ?loc (Logic_const.here_label, t)
  | "dangling", _ | "valid", _ | "valid_read", _ | "initialized", _ ->
    Options.fatal
      "Mismatch between the function name ('%s') and the number of parameters \
       (%d)"
      name
      (List.length args)
  | _ ->
    Options.fatal "Unsupported function '%s'" name

(* [extract_quantifiers ~loc args] iterates over each argument in [args] and if
   that argument contains a non-explicit range, tries to extract a universal
   quantifier representing the range and returns an updated argument for this
   quantifier.

   The cases in the function comments correspond to the cases described in
   [call_with_tset]. *)
let extract_quantifiers ~loc args =
  let args = List.rev args in
  List.fold_left
    (fun (args, quantifiers) arg ->
       let arg, quantifiers =
         match arg.term_node with
         | TAddrOf(TVar _, TIndex({ term_node = Trange _ }, TNoOffset)) ->
           (* Case A: explicit range *)
           arg, quantifiers
         | TAddrOf(TVar ({ lv_type = Ctype (TArray _) } as lv), toffset) ->
           if has_set_as_index toffset then
             (* Case B: non-explicit range, try to extract quantifiers with
                range elimination. *)
             try
               let toffset', quantifiers' =
                 eliminate_ranges_from_index_of_toffset ~loc toffset quantifiers
               in
               let lty_noset =
                 Logic_typing.type_of_pointed @@
                 if Logic_const.is_set_type arg.term_type then
                   Logic_const.type_of_element arg.term_type
                 else
                   arg.term_type
               in
               let arg' =
                 Logic_utils.mk_logic_AddrOf ~loc (TVar lv, toffset') lty_noset
               in
               arg', quantifiers'
             with Range_elimination_exception ->
               (* Case C: range elimination failed *)
               arg, quantifiers
           else
             (* Case C: no range in the offsets *)
             arg, quantifiers
         | _ ->
           (* Case A or C: either explicit range or no range. *)
           arg, quantifiers
       in
       (arg :: args, quantifiers)
    )
    ([], [])
    args

(* [call_with_tset
      ~loc
      ~arg_from_range
      ~arg_from_term
      ~prepend_n_args
      kf
      name
      ctx
      env
      args
      p]
   creates a call to the E-ACSL memory builtin identified by [name] with the
   given tset [args].

   [arg_from_range ~loc kf env rev_args ptr r p] is a function that converts an
   argument of the form [ptr + r] where [ptr] is an address and [r] a range into
   a list of arguments that can be passed to a built-in function and add them in
   reverse order to the [rev_args] parameter list. For instance for the built-in
   [\initialized(ptr + r)], [ptr + r] will be turned into [[ptr'; size]] where
   [ptr'] is the address of the start of the range and [size] is the size of the
   range, and will be returned as [size :: ptr' :: rev_args].

   [arg_from_term ~loc kf env rev_args t p] is a function that converts a term
   without range argument [t] into a list of arguments that can be passed to a
   built-in function and add them in reverse order to the [rev_args] parameter
   list. For instance for the built-in [\valid(t)], [t] will be turned into
   [[e; size; base; base_addr]] where [e] is the value representing [t], [size]
   is the size of the memory under study, [base] is the value [ptr] if [t] can
   be represented by the expression [ptr + i], and [base_addr] if the value
   [&ptr] if [t] can be represented by the expression [ptr + i]. They will be
   returned as [base_addr :: base :: size :: e :: rev_args].

   If [prepend_n_args], then the number of arguments in args is prepended to the
   list of arguments given to the builtin.

   Since each argument in [args] is a tset, it can contains ranges. For now,
   only the following cases are supported:
   A: [\builtin(ptr+r)] where [ptr] is an address and [r] a range or
    [\builtin(t[r])] or
    [\builtin(t[i_1]...[i_n])] where [t] is dynamically allocated
                               and all the indexes are integers,
                               except the last one which is a range
    The generated code is a SINGLE call to the corresponding E-ACSL builtin
   B: [\builtin(t[i_1]...[i_n])] where [t] is NOT dynamically allocated
                               and the indexes are integers or ranges
    The generated code is a SET OF calls to the corresponding E-ACSL builtin
   C: Any other use of ranges/No range
    Call [arg_from_term] which performs the translation for
    range free terms, and raises Not_yet if it ever encounters a range.
   Example for case:
   A: [\valid(&t[3..5])]
    Contiguous locations -> a single call to [__e_acsl_valid]
   B: [\valid(&t[4][3..5][2])]
    NON-contiguous locations -> multiple calls (3) to [__e_acsl_valid] *)
let call_with_tset
    ~adata
    ~loc
    ~arg_from_range
    ~arg_from_term
    ?(prepend_n_args=false)
    kf
    name
    ctx
    env
    args
    p
  =
  let args, quantifiers = extract_quantifiers ~loc args in
  match quantifiers with
  | _ :: _ ->
    (* Some quantifiers have been extracted from the arguments, we need to build
       a new predicate with these quantifiers and the updated arguments. *)
    let p_quantified = fname_to_pred ~loc name args in
    let p_quantified =
      List.fold_left
        (fun p (tmin, lv, tmax) ->
           (* \forall integer tlv; tmin <= tlv <= tmax ==> p *)
           let tlv = Logic_const.tvar ~loc lv in
           let lower_bound = Logic_const.prel ~loc (Rle, tmin, tlv) in
           let upper_bound = Logic_const.prel ~loc (Rle, tlv, tmax) in
           let bound = Logic_const.pand ~loc (lower_bound, upper_bound) in
           let bound_imp_p = Logic_const.pimplies ~loc (bound, p) in
           Logic_const.pforall ~loc ([lv], bound_imp_p)
        )
        p_quantified
        quantifiers
    in
    (* There's no more quantifiers in the arguments now, we can call back
       [predicate_to_exp] to translate the predicate as usual *)
    Typing.preprocess_predicate (Env.Local_vars.get env) p_quantified;
    !predicate_to_exp_ref ~adata kf env p_quantified
  | [] ->
    (* No arguments require quantifiers, so we can directly translate the
       predicate *)
    let n_args, rev_args, adata, env =
      List.fold_left
        (fun (n_args, rev_args, adata, env) t ->
           let rev_args, adata, env =
             if Misc.is_bitfield_pointers t.term_type then
               Error.not_yet "bitfield pointer";
             match t.term_node with
             | TBinOp(PlusPI,
                      ptr,
                      ({ term_node = Trange _ } as r)) ->
               if Misc.is_set_of_ptr_or_array ptr.term_type then
                 Error.not_yet
                   "arithmetic over set of pointers or arrays"
               else
                 (* Case A *)
                 arg_from_range ~adata ~loc kf env rev_args ptr r p
             | TAddrOf(TVar lv, TIndex({ term_node = Trange _ } as r, TNoOffset)) ->
               (* Case A *)
               assert (Logic_const.is_set_type t.term_type);
               let lty_noset = Logic_const.type_of_element t.term_type in
               let ptr =
                 Logic_const.term ~loc (TStartOf (TVar lv, TNoOffset)) lty_noset
               in
               arg_from_range ~adata ~loc kf env rev_args ptr r p
             | _ ->
               (* Case A, B with failed range elimination or C *)
               arg_from_term ~adata ~loc kf env rev_args t p
           in
           let n_args = n_args + 1 in
           n_args, rev_args, adata, env
        )
        (0, [], adata, env)
        args
    in
    (* The arguments were built in reverse, reorder them *)
    let args = List.rev rev_args in
    let args =
      if prepend_n_args then
        Cil.integer ~loc n_args :: args
      else
        args
    in
    let _, e, env =
      Env.new_var
        ~loc
        ~name
        env
        kf
        None
        ctx
        (fun v _ -> [
             Smart_stmt.rtl_call ~loc ~result:(Cil.var v) name args
           ])
    in
    e, adata, env

(* \initialized and \separated *)
let call_with_size ~adata ~loc kf name ctx env args p =
  assert (name = "initialized" || name = "separated");
  let arg_from_term ~adata ~loc kf env rev_args t _p =
    let ptr, size, adata, env = term_to_ptr_and_size ~adata ~loc kf env t in
    size :: ptr :: rev_args, adata, env
  in
  let arg_from_range ~adata ~loc kf env rev_args ptr r p =
    let ptr, size, adata, env =
      range_to_ptr_and_size ~adata ~loc kf env ptr r p
    in
    size :: ptr :: rev_args, adata, env
  in
  let prepend_n_args = Datatype.String.equal name "separated" in
  call_with_tset
    ~adata
    ~loc
    ~arg_from_term
    ~arg_from_range
    ~prepend_n_args
    kf
    name
    ctx
    env
    args
    p

(* \valid and \valid_read *)
let call_valid ~adata ~loc kf name ctx env t p =
  assert (name = "valid" || name = "valid_read");
  let arg_from_term ~adata ~loc kf env rev_args t _p =
    let ptr, size, adata, env = term_to_ptr_and_size ~adata ~loc kf env t in
    let base, base_addr = Misc.ptr_base_and_base_addr ~loc ptr in
    base_addr :: base :: size :: ptr :: rev_args, adata, env
  in
  let arg_from_range ~adata ~loc kf env rev_args ptr r p =
    let ptr, size, adata, env =
      range_to_ptr_and_size ~adata ~loc kf env ptr r p
    in
    let base, base_addr = Misc.ptr_base_and_base_addr ~loc ptr in
    base_addr :: base :: size :: ptr :: rev_args, adata, env
  in
  let prepend_n_args = false in
  call_with_tset
    ~adata
    ~loc
    ~arg_from_term
    ~arg_from_range
    ~prepend_n_args
    kf
    name
    ctx
    env
    [ t ]
    p
