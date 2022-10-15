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

(** Code generation for libc functions *)

open Cil_types

(* Retrieve the name of the caller function. [vorig_name] is used instead of
   [vname] because some plugins like "Variadic" may change the value of [vname]
   for some functions like [sprintf]. *)
let get_caller_name caller =
  caller.vorig_name

let is_writing_memory caller =
  match get_caller_name caller with
  (* Input / output functions *)
  (* - Formatted *)
  | "sprintf" | "snprintf" | "vsprintf" | "vsnprintf" | "swprintf" | "vswprintf"
  | "scanf" | "fscanf" | "sscanf" | "vscanf" | "vfscanf" | "vsscanf" | "wscanf"
  | "fwscanf" | "swscanf" | "vwscanf" | "vfwscanf" | "vswscanf"
  (* - Unformatted *)
  | "gets" | "fgets" | "fgetws"
  (* - Direct *)
  | "fread"

  (* Byte strings *)
  (* - Conversions *)
  | "strtol" | "strtoll" | "strtoul" | "strtoull" | "strtof" | "strtod"
  | "strtold" | "strtoimax" | "strtoumax"
  (* - String manipulation *)
  | "strcpy" | "strncpy" | "strcat" | "strncat" | "strxfrm"
  (* - Character array manipulation *)
  | "memset" | "memcpy" | "memmove"

  (* Multi-byte strings *)
  | "mbtowc" | "wctomb" | "mbstowcs" | "wcstombs" | "mbrtowc" | "wcrtomb"
  | "mbsrtowcs" | "wcsrtombs"

  (* Wide strings *)
  (* - Conversions *)
  | "wcstol" | "wcstoll" | "wcstoul" | "wcstoull" | "wcstof" | "wcstod"
  | "wcstold" | "wcstoimax" | "wcstoumax"
  (* - Wide string manipulation *)
  | "wcscpy" | "wcsncpy" | "wcscat" | "wcsncat" | "wcsxfrm"
  (* - Wide character array manipulation *)
  | "wmemset" | "wmemcpy" | "wmemmove"
    -> true

  | _ -> false

let () =
  Prepare_ast.is_libc_writing_memory_ref := is_writing_memory

(** [get_result_var ~loc ~name kf ty env result_opt] returns an lvalue
    representing the result of the call to the libc function. If [result_opt]
    is [Some var] then this lvalue is directly returned, but if the return value
    of the function was not saved and [result_opt] is [None], then a new value
    is created to hold the result of the call. *)
let get_result_var ~loc ~name kf ty env result_opt =
  match result_opt with
  | Some result -> result, env
  | None ->
    let vi, _, env =
      Env.new_var
        ~loc
        ~scope:Varname.Function
        ~name:(name ^ "_res")
        env
        kf
        None
        ty
        (fun _ _ -> [])
    in
    Cil.var vi, env

(** [rtl_call_to_new_var ~loc ~name env kf ty fname args] creates a call to the
    RTL function [fname] with arguments [args] and stores the result in a new
    variable named [name]. *)
let rtl_call_to_new_var ~loc ~name env kf ty fname args =
  let vi, e, env =
    Env.new_var
      ~loc
      ~scope:Varname.Function
      ~name
      env
      kf
      None
      ty
      (fun _ _ -> [])
  in
  let stmt =
    Smart_stmt.rtl_call ~loc ~result:(Cil.var vi) fname args
  in
  vi, e, stmt, env

(** [strlen ~loc ~name env kf e] generates a call to the RTL function
    [__e_acsl_builtin_strlen] and stores the result in a new variable named
    [name].
    The E-ACSL built-in version of [strlen] is used to be able to work even if
    [string.h] was not included in the original code. Moreover, the built-in
    version already check the preconditions of the function so it is not
    necessary to generate more RTE checks. *)
let strlen ~loc ~name env kf e =
  rtl_call_to_new_var
    ~loc
    ~name
    env
    kf
    Cil.theMachine.typeOfSizeOf
    "builtin_strlen"
    [ e ]

(** [wrong_number_of_arguments name] aborts the execution of E-ACSL with a
    message about the number of arguments for [name]. *)
let wrong_number_of_arguments name =
  Options.fatal
    "Wrong number of arguments for E-ACSL built-in '%s'. Should have been \
     caught by Frama-C kernel before."
    name

(** [lval_to_term ~loc lval] converts the lvalue [lval] to a term. *)
let lval_to_term ~loc lval =
  let ty = Cil.typeOfLval lval in
  Logic_const.term ~loc (TLval (Logic_utils.lval_to_term_lval lval)) (Ctype ty)

(** [zarith ~loc bop t1 t2] creates an integer term representing the arithmetic
    operation [t1 bop t2]. *)
let zarith ~loc bop t1 t2 =
  (* Check that we are building an arithmetic operation *)
  (match bop with
   | PlusA | MinusA | Mult | Div | Mod | Shiftlt | Shiftrt -> ()
   | PlusPI | MinusPI | MinusPP | Lt | Gt | Le | Ge | Eq | Ne | BAnd
   | BXor | BOr | LAnd | LOr ->
     Options.fatal
       "Using Libc.zarith to build '%a' instead of an arithmetic operation"
       Printer.pp_binop bop);
  (* Coerce arguments to integers *)
  let t1 = Logic_utils.numeric_coerce Linteger t1 in
  let t2 = Logic_utils.numeric_coerce Linteger t2 in
  (* Create binop term *)
  Logic_const.term ~loc (TBinOp (bop, t1, t2)) Linteger

(** [check_integer_bounds ~from target] checks if the bounds need to be checked
    while coercing an integer variable from the kind [from] to the kind
    [target].
    @return a pair where the first element is true if the lower bound needs to
    be checked and false otherwise, and the second element is true if the upper
    bound needs to be checked and false otherwise. *)
let check_integer_bounds ~from target =
  let from_bitsize = Cil.bitsSizeOfInt from in
  let target_bitsize = Cil.bitsSizeOfInt target in
  match Cil.isSigned from, Cil.isSigned target with
  | true, true | false, false ->
    let check_bounds = from_bitsize > target_bitsize in
    check_bounds, check_bounds
  | true, false ->
    let from_max = Cil.max_signed_number from_bitsize in
    let target_max = Cil.max_unsigned_number target_bitsize in
    true, from_max > target_max
  | false, true ->
    let from_max = Cil.max_unsigned_number from_bitsize in
    let target_max = Cil.max_signed_number target_bitsize in
    false, from_max > target_max

(** [term_to_sizet_exp ~loc ?check_lower_bound kf env t] translates the term [t]
    to a C expression of type [size_t]. If the term is a GMP value then bounding
    checks are added to ensure that the term holds in the C type.
    If [check_lower_bound] is set to false, then the lower bound check is not
    performed. *)
let term_to_sizet_exp ~loc ~name ?(check_lower_bound=true) kf env t =
  Typing.type_term ~use_gmp_opt:false ~lenv:(Env.Local_vars.get env) t;
  match Typing.get_number_ty ~lenv:(Env.Local_vars.get env) t with
  | Typing.Gmpz ->
    let e, _, env =
      Translate_utils.gmp_to_sizet
        ~adata:Assert.no_data
        ~loc
        ~name
        ~check_lower_bound
        kf
        env
        t
    in
    e, env
  | Typing.(C_integer _ | C_float _) as nty ->
    (* We know that [t] can be translated to a C type, so we start with that *)
    let e, _, env = Translate_terms.to_exp ~adata:Assert.no_data kf env t in
    (* Then we can check if the expression will fit in a [size_t] *)
    let sizet = Cil.(theMachine.typeOfSizeOf) in
    let sizet_kind = Cil.(theMachine.kindOfSizeOf) in
    let check_lower_bound, check_upper_bound =
      let lower, upper =
        match nty with
        | Typing.C_integer t_kind ->
          check_integer_bounds ~from:t_kind sizet_kind
        | Typing.C_float _ -> true, true
        | _ -> assert false
      in
      lower && check_lower_bound, upper
    in
    let stmts, env =
      if check_lower_bound then begin
        let lower_guard = Cil.mkBinOp ~loc Ge e (Cil.zero ~loc) in
        let lower_guard_pp =
          Logic_const.prel ~loc (Rge, t, Cil.lzero ~loc ())
        in
        let adata, env = Assert.empty ~loc kf env in
        let adata, env = Assert.register_term ~loc env t e adata in
        let assertion, env =
          Assert.runtime_check
            ~adata
            ~pred_kind:Assert
            RTE
            kf
            env
            lower_guard
            lower_guard_pp
        in
        [ assertion ], env
      end else [], env
    in
    let stmts, env =
      if check_upper_bound then begin
        let sizet_max_z = Cil.max_unsigned_number (Cil.bitsSizeOf sizet) in
        let sizet_max_t = Logic_const.tint ~loc sizet_max_z in
        let sizet_max_e =
          Cil.kinteger64 ~loc ~kind:sizet_kind sizet_max_z
        in
        let upper_guard_pp = Logic_const.prel ~loc (Rle, t, sizet_max_t) in
        let upper_guard = Cil.mkBinOp ~loc Le e sizet_max_e in
        let adata, env = Assert.empty ~loc kf env in
        let adata, env = Assert.register_term ~loc env t e adata in
        let adata, env =
          Assert.register ~loc env "SIZE_MAX" sizet_max_e adata
        in
        let assertion, env =
          Assert.runtime_check
            ~adata
            ~pred_kind:Assert
            RTE
            kf
            env
            upper_guard
            upper_guard_pp
        in
        assertion :: stmts, env
      end else
        stmts, env
    in
    (* If no assertions have been generated we can directly return the
       translated expression, otherwise we create a [size_t] variable to hold
       the conversion*)
    if stmts = [] then
      e, env
    else
      let _, e, env =
        Env.new_var
          ~loc
          env
          kf
          None
          sizet
          (fun vi _ ->
             let assigns = Smart_stmt.assigns ~loc ~result:(Cil.var vi) e in
             List.rev (assigns :: stmts))
      in
      e, env
  | Typing.(Rational | Real) ->
    Env.not_yet env "cast of rational or real to size_t"
  | Typing.Nan ->
    Options.fatal
      "Trying to translate a term that is not an integer or a C type: %a"
      Printer.pp_term t

(** Code generation of [update_memory_model] for [strcat] and [strncat]. *)
let process_strcat ~loc ?result env kf ?size_e dest_e src_e =
  let src_size_vi, src_size_e, src_size_stmt, env =
    strlen ~loc ~name:"strcat_src_size" env kf src_e
  in
  let pre_stmts = [ src_size_stmt ] in
  let pre_stmts =
    match size_e with
    | Some size_e ->
      let src_size_if_stmt =
        Smart_stmt.if_stmt
          ~loc
          ~cond:(Cil.mkBinOp ~loc Lt size_e src_size_e)
          (Cil.mkBlock [
              Smart_stmt.assigns ~loc ~result:(Cil.var src_size_vi) size_e
            ])
      in
      src_size_if_stmt :: pre_stmts
    | None -> pre_stmts
  in
  let dest_size_vi, _, dest_size_stmt, env =
    strlen ~loc ~name:"strcat_dest_size" env kf dest_e
  in
  let pre_stmts = dest_size_stmt :: pre_stmts in
  let env = Env.push env in
  let src_size_term = Cil.cvar_to_term ~loc src_size_vi in
  let dest_size_term = Cil.cvar_to_term ~loc dest_size_vi in
  let n_t = zarith ~loc PlusA src_size_term dest_size_term in
  let n_t = zarith ~loc PlusA n_t (Cil.lone ~loc ()) in
  (* By construction, [n_t] cannot be negative so we do not need to check the
     lower bound. *)
  let n, env =
    term_to_sizet_exp ~loc ~name:"size" ~check_lower_bound:false kf env n_t
  in
  (* The specifications of [strcat] and [strncat] indicate that these functions
     write only from [dest_e + strlen(dest)] to
     [dest_e + strlen(dest_e) + strlen(src_e) + 1]. However since they require
     the [dest_e] string to be valid from [dest_e] to
     [dest_e + strlen(dest_e) +1], we can call initialize from [dest_e] to
     [dest_e + strlen(dest_e) + strlen(src_e) + 1]. This allows us to only
     compute the size of the initialization (in [n]) instead of computing the
     start pointer and the size. *)
  let initialize = Smart_stmt.rtl_call ~loc "initialize" [ dest_e; n ] in
  let initialize_blk, env =
    Env.pop_and_get env initialize ~global_clear:false Env.Middle
  in

  let initialize_blk = Smart_stmt.block_stmt initialize_blk in
  let env =
    List.fold_right
      (fun pre_stmt env -> Env.add_stmt env pre_stmt)
      pre_stmts
      env
  in
  let env = Env.add_stmt ~post:true env initialize_blk in
  result, env

let update_memory_model ~loc ?result env kf caller args =
  let name = get_caller_name caller in
  let post = true in
  match name, args with
  | "memset", [ dest_e; _; size_e ] | "memcpy", [ dest_e; _; size_e ]
  | "memmove", [ dest_e; _; size_e ] ->
    let initialize = Smart_stmt.rtl_call ~loc "initialize" [dest_e; size_e] in
    let env = Env.add_stmt ~post env initialize in
    result, env
  | "memset", _ | "memcpy", _ | "memmove", _ -> wrong_number_of_arguments name

  | "fread", [ buffer_e; size_e; _; _ ] ->
    let result, env =
      get_result_var ~loc ~name kf Cil.theMachine.typeOfSizeOf env result
    in
    let env = Env.push env in
    let result_t = lval_to_term ~loc result in
    let size_t, env =
      let vi, env =
        match size_e.enode with
        | Lval (Var vi, NoOffset) -> vi, env
        | _ ->
          let vi, _, env =
            Env.new_var
              ~loc
              env
              kf
              None
              (Cil.typeOf size_e)
              (fun vi _ ->
                 [ Smart_stmt.assigns ~loc ~result:(Cil.var vi) size_e ])
          in
          vi, env
      in
      Cil.cvar_to_term ~loc vi, env
    in
    let n_t = zarith ~loc Mult result_t size_t in
    (* By construction, [n_t] cannot be negative so we do not need to check the
       lower bound *)
    let n, env =
      term_to_sizet_exp ~loc ~name:"size" ~check_lower_bound:false kf env n_t
    in
    let initialize = Smart_stmt.rtl_call ~loc "initialize" [buffer_e; n] in
    let initialize_blk, env =
      Env.pop_and_get env initialize ~global_clear:false Env.Middle
    in
    let env =
      Env.add_stmt ~post env (Smart_stmt.block_stmt initialize_blk)
    in
    Some result, env
  | "fread", _ -> wrong_number_of_arguments name

  | "strcpy", [ dest_e; src_e ] ->
    let src_size_vi, _, src_size_stmt, env =
      strlen ~loc ~name:"strcpy_src_size" env kf src_e
    in
    let env = Env.push env in
    let src_size_t = Cil.cvar_to_term ~loc src_size_vi in
    let n_t =
      zarith ~loc PlusA src_size_t (Cil.lone ~loc ())
    in
    (* By construction, [n_t] cannot be negative so we do not need to check the
       lower bound *)
    let n, env =
      term_to_sizet_exp ~loc ~name:"size" ~check_lower_bound:false kf env n_t
    in
    let initialize = Smart_stmt.rtl_call ~loc "initialize" [ dest_e; n ] in
    let initialize_blk, env =
      Env.pop_and_get env initialize ~global_clear:false Env.Middle
    in
    let initialize_blk = Smart_stmt.block_stmt initialize_blk in
    let env = Env.add_stmt env src_size_stmt in
    let env = Env.add_stmt ~post env initialize_blk in
    result, env
  | "strcpy", _ -> wrong_number_of_arguments name

  | "strncpy" , [ dest_e; _; size_e ] ->
    let initialize =
      Smart_stmt.rtl_call ~loc "initialize" [ dest_e; size_e ]
    in
    let env = Env.add_stmt ~post env initialize in
    result, env
  | "strncpy", _ -> wrong_number_of_arguments name

  | "strcat", [ dest_e; src_e ] ->
    process_strcat ~loc ?result env kf dest_e src_e
  | "strcat", _ -> wrong_number_of_arguments name

  | "strncat", [ dest_e; src_e; size_e ] ->
    process_strcat ~loc ?result env kf ~size_e dest_e src_e
  | "strncat", _ -> wrong_number_of_arguments name

  | "sprintf", buffer_e :: _ :: _  ->
    let result, env = get_result_var ~loc ~name kf Cil.intType env result in
    let result_e = Smart_exp.lval ~loc result in
    let env = Env.push env in
    let result_t = lval_to_term ~loc result in
    let n_t = zarith ~loc PlusA result_t (Cil.lone ~loc ()) in
    (* We already add the guard [result >= 0] before calling
       [__e_acsl_initialize] so we do not need to check the lower bound here. *)
    let n, env =
      term_to_sizet_exp ~loc ~name:"size" ~check_lower_bound:false kf env n_t
    in
    let initialize = Smart_stmt.rtl_call ~loc "initialize" [ buffer_e; n ] in
    let then_blk, env =
      Env.pop_and_get env initialize ~global_clear:false Env.Middle
    in
    let if_res_pos_stmt =
      Smart_stmt.if_stmt
        ~loc
        ~cond:(Cil.mkBinOp ~loc Ge result_e (Cil.zero ~loc))
        then_blk
    in
    let env = Env.add_stmt ~post env if_res_pos_stmt in
    Some result, env
  | "sprintf", _ -> wrong_number_of_arguments name

  | "snprintf", buffer_e :: size_e :: _ :: _ ->
    let result, env = get_result_var ~loc ~name kf Cil.intType env result in
    let result_e = Smart_exp.lval ~loc result in
    let env = Env.push env in
    let n_vi, n_e, env =
      Env.new_var
        ~loc
        ~scope:Varname.Block
        ~name:"n"
        env
        kf
        None
        Cil.theMachine.typeOfSizeOf
        (fun _ _ -> [])
    in
    let env = Env.push env in
    let result_t = lval_to_term ~loc result in
    let res_plus_one_t = zarith ~loc PlusA result_t (Cil.lone ~loc ()) in
    (* We already add the guard [result >= 0] before calling
       [__e_acsl_initialize] so we do not need to check the lower bound here. *)
    let res_plus_one_e, env =
      term_to_sizet_exp
        ~loc
        ~name:"result"
        ~check_lower_bound:false
        kf
        env
        res_plus_one_t
    in
    let assigns_res_plus_one_stmt =
      Smart_stmt.assigns ~loc ~result:(Cil.var n_vi) res_plus_one_e
    in
    let assigns_res_plus_one_blk, env =
      Env.pop_and_get
        env
        assigns_res_plus_one_stmt
        ~global_clear:false
        Env.Middle
    in
    let assigns_n_stmt =
      Smart_stmt.if_stmt
        ~loc
        ~cond:(Cil.mkBinOp ~loc Le size_e result_e)
        (Cil.mkBlock [ Smart_stmt.assigns ~loc ~result:(Cil.var n_vi) size_e ])
        ~else_blk:assigns_res_plus_one_blk
    in
    let initialize = Smart_stmt.rtl_call ~loc "initialize" [ buffer_e; n_e ] in
    let blk_stmt =
      Smart_stmt.block_from_stmts [
        assigns_n_stmt;
        initialize
      ]
    in
    let blk, env =
      Env.pop_and_get env blk_stmt ~global_clear:false Env.Middle
    in
    let res_pos = Cil.mkBinOp ~loc Ge result_e (Cil.zero ~loc) in
    let size_strict_pos = Cil.mkBinOp ~loc Gt size_e (Cil.zero ~loc) in
    let if_res_pos_stmt =
      Smart_stmt.if_stmt
        ~loc
        ~cond:(Cil.mkBinOp ~loc LAnd res_pos size_strict_pos)
        blk
    in
    let env = Env.add_stmt ~post env if_res_pos_stmt in
    Some result, env
  | "snprintf", _ ->
    wrong_number_of_arguments name

  | _ when is_writing_memory caller ->
    Options.warning ~once:true
      "Memory model not yet supported for standard library function '%s'. \
       Check of memory locations from now on may be incorrect."
      name;
    let sound_verdict_vi = Prepare_ast.sound_verdict () in
    let unsound =
      Smart_stmt.assigns ~loc ~result:(Cil.var sound_verdict_vi) (Cil.zero ~loc)
    in
    let env = Env.add_stmt ~post env unsound in
    result, env
  | _ ->
    (* If this error is raised, check that the call to
       [Libc.update_memory_model] is guarded with [Libc.is_writing_memory] and
       that [Libc.is_writing_memory] is up to date. *)
    Options.fatal
      "Function '%s' is not a standard library function that need the memory \
       model to be checked."
      name
