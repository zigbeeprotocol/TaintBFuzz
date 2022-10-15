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

(** Module with the context to hold the data contributing to an assertion and
    general functions to create assertion statements. *)

open Cil_types
open Analyses_types
open Analyses_datatype

(** Type holding information about the C variable representing the assertion
    data. *)
type data = {
  data_registered: bool;
  (** Indicates if some data have been registered in the context or not. *)
  data_vi: varinfo;
  (** [varinfo] representing the C variable for the assertion data. *)
  data_ptr: exp;
  (** [exp] representing a pointer to the C variable for the assertion data. *)
}

(** External type representing the assertion context. Either [Some data] if we
    want to register some data in the context of [None] if we do not want to. *)
type t = data option

let no_data = None

(** C type for the [assert_data_t] structure. *)
let assert_data_ctyp_lazy =
  lazy (Globals.Types.find_type
          Logic_typing.Typedef (Functions.RTL.mk_api_name "assert_data_t"))

let empty ~loc kf env =
  let assert_data_cty = Lazy.force assert_data_ctyp_lazy in
  let data_vi, _, env =
    Env.new_var
      ~loc
      ~name:"assert_data"
      env
      kf
      None
      assert_data_cty
      (fun vi _ ->
         [ Smart_stmt.struct_local_init
             ~loc
             vi
             [ "values", Smart_exp.null ~loc ] ])
  in
  let data =
    { data_registered = false;
      data_vi;
      data_ptr = Cil.mkAddrOfVi data_vi }
  in
  Some data , env

let with_data_from ~loc kf env from =
  match from with
  | Some from ->
    let adata, env = empty ~loc kf env in
    let adata = Option.get adata in
    let env =
      if from.data_registered then
        let stmt =
          Smart_stmt.rtl_call
            ~loc
            "assert_copy_values"
            [ adata.data_ptr; from.data_ptr ]
        in
        Env.add_stmt env stmt
      else env
    in
    Some { adata with data_registered = from.data_registered }, env
  | None -> None, env

let merge_right ~loc env adata1 adata2 =
  match adata1, adata2 with
  | Some adata1, Some adata2 when adata1.data_registered ->
    let stmt =
      Smart_stmt.rtl_call
        ~loc
        "assert_copy_values"
        [ adata2.data_ptr; adata1.data_ptr ]
    in
    let adata2 =
      { adata2 with
        data_registered = true }
    in
    let env = Env.add_stmt env stmt in
    Some adata2, env
  | Some _, Some adata | None, Some adata -> Some adata, env
  | Some _, None | None, None -> None, env

let clean ~loc env adata =
  match adata with
  | Some { data_registered; data_ptr } when data_registered->
    let clean_stmt = Smart_stmt.rtl_call ~loc "assert_clean" [ data_ptr ] in
    Env.add_stmt env clean_stmt
  | Some _ | None ->
    env

let ikind_to_string = function
  | IBool -> "bool"
  | IChar -> "char"
  | ISChar -> "schar"
  | IUChar -> "uchar"
  | IInt -> "int"
  | IUInt -> "uint"
  | IShort -> "short"
  | IUShort -> "ushort"
  | ILong -> "long"
  | IULong -> "ulong"
  | ILongLong -> "longlong"
  | IULongLong -> "ulonglong"

let do_register_data ~loc env { data_ptr } name e =
  let ty = Cil.typeOf e in
  let fct, args =
    if Gmp_types.Z.is_t ty then
      "mpz", [ Cil.zero ~loc; e ]
    else if Gmp_types.Q.is_t ty then
      "mpq", [ e ]
    else
      match Cil.unrollType ty with
      | TInt (ikind, _) -> ikind_to_string ikind, [ Cil.zero ~loc; e ]
      | TFloat (FFloat, _) -> "float", [ e ]
      | TFloat (FDouble, _) -> "double", [ e ]
      | TFloat (FLongDouble, _) -> "longdouble", [ e ]
      | TPtr _ -> "ptr", [ e ]
      | TArray _ -> "array", [ e ]
      | TFun _ -> "fun", []
      | TComp ({ cstruct = true }, _) -> "struct", []
      | TComp ({ cstruct = false }, _) -> "union", []
      | TEnum ({ ekind }, _) -> ikind_to_string ekind, [ Cil.one ~loc; e ]
      | TVoid _
      | TBuiltin_va_list _ -> "other", []
      | TNamed _ ->
        Options.fatal
          "named types in '%a' should have been unrolled"
          Printer.pp_typ ty
  in
  let fct = "assert_register_" ^ fct in
  let name = Cil.mkString ~loc name in
  let args = data_ptr :: name :: args in
  let stmt = Smart_stmt.rtl_call ~loc fct args in
  Env.add_stmt env stmt

let register ~loc env ?(force=false) name e adata =
  if Options.Assert_print_data.get () then
    match adata, e.enode with
    | Some adata, Const _ when not force ->
      (* By default, do not register constant expressions because the name of
         the data will be its value. For instance in expression [a + 3], the
         data [a] needs to be registered, but [3] already appears in the
         predicate message, and trying to register it will result in a data with
         name "3" and value [3].
         The registration can be forced for expressions like [sizeof(int)] for
         instance that are [Const] values but not directly known. *)
      Some adata, env
    | Some adata, _ ->
      let adata = { adata with data_registered = true } in
      Some adata, do_register_data ~loc env adata name e
    | None, _ -> None, env
  else
    adata, env

let register_term ~loc env ?force t e adata =
  let name = Format.asprintf "@[%a@]" Printer.pp_term t in
  register ~loc env name ?force e adata

let register_pred ~loc env ?force p e adata =
  if Env.annotation_kind env == RTE then
    (* When translating RTE, we do not want to print the result of the predicate
       because they should be the only predicate in an assertion clause. *)
    adata, env
  else
    let name = Format.asprintf "@[%a@]" Printer.pp_predicate p in
    register ~loc env name ?force e adata

let register_pred_or_term ~loc env ?force pot e adata =
  match pot with
  | PoT_term t -> register_term ~loc env ?force t e adata
  | PoT_pred p -> register_pred ~loc env ?force p e adata

let kind_to_string loc k =
  Cil.mkString
    ~loc
    (Format.asprintf "%a" Annotation_kind.pretty k)

let runtime_check_with_msg ~adata ~loc ?(name="") msg ~pred_kind kind kf env predicate_e =
  let env = Env.push env in
  let data_registered, data_ptr, data_vi, env =
    match adata with
    | Some { data_registered; data_ptr; data_vi } ->
      data_registered, data_ptr, data_vi, env
    | None ->
      let adata, env = empty ~loc kf env in
      let adata = Option.get adata in
      false, adata.data_ptr, adata.data_vi, env
  in
  let blocking =
    match pred_kind with
    | Assert -> Cil.one ~loc
    | Check -> Cil.zero ~loc
    | Admit ->
      Options.fatal "No runtime check should be generated for 'admit' clauses"
  in
  let kind = kind_to_string loc kind in
  let pred_txt = Cil.mkString ~loc msg in
  let start_pos = fst loc in
  let file =
    Cil.mkString
      ~loc
      (Filepath.Normalized.to_pretty_string start_pos.Filepath.pos_path)
  in
  let fct = Cil.mkString ~loc (Functions.RTL.get_original_name kf) in
  let line = Cil.integer ~loc start_pos.Filepath.pos_lnum in
  let stmts =
    [ Smart_stmt.assigns_field ~loc data_vi "line" line;
      Smart_stmt.assigns_field ~loc data_vi "fct" fct;
      Smart_stmt.assigns_field ~loc data_vi "file" file;
      Smart_stmt.assigns_field ~loc data_vi "pred_txt" pred_txt;
      Smart_stmt.assigns_field ~loc data_vi "kind" kind;
      Smart_stmt.assigns_field ~loc data_vi "blocking" blocking ]
  in
  let stmts =
    if Datatype.String.equal name "" then
      stmts
    else
      Smart_stmt.assigns_field
        ~loc
        data_vi
        "name"
        (Cil.mkString ~loc name)
      :: stmts
  in
  let stmts =
    Smart_stmt.rtl_call ~loc "assert" [ predicate_e; data_ptr ] :: stmts
  in
  let stmts=
    if data_registered then
      Smart_stmt.rtl_call ~loc "assert_clean" [ data_ptr ] :: stmts
    else
      stmts
  in
  let block, env =
    Env.pop_and_get
      env
      (Smart_stmt.block_from_stmts (List.rev stmts))
      ~global_clear:false
      Env.Middle
  in
  Smart_stmt.block_stmt block, env

let runtime_check ~adata ~pred_kind kind kf env e p =
  let loc = p.pred_loc in
  let name = String.concat "/" p.pred_name in
  let p = { p with pred_name = [] } in
  let msg = Format.asprintf "%a@?" Printer.pp_predicate p in
  runtime_check_with_msg ~adata ~loc ~name msg ~pred_kind kind kf env e
