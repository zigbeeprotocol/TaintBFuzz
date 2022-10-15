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
open Va_types
open Options
module List = Extends.List
module Typ = Extends.Typ

type call_builder  = Cil_types.exp -> Cil_types.exp list -> Cil_types.instr

let pp_prototype name fmt tparams =
  Format.fprintf fmt "%s(%a)"
    name
    (Pretty_utils.pp_list ~sep:", " Printer.pp_typ) tparams

let pp_overload name fmt l =
  let prototypes = List.map fst l in
  Pretty_utils.pp_list ~sep:"@\n" (pp_prototype name) fmt prototypes


let new_globals : (global list) ref = ref []

(* State to store the number of fallback functions generated for a particular
   function name. This number is used to generate a unique function name. *)
module Fallback_counts =
  State_builder.Hashtbl
    (Datatype.String.Hashtbl)
    (Datatype.Int)
    (struct
      let size = 17
      let name = "fallback_counts"
      let dependencies = [ Options.Enabled.self; Options.Strict.self ]
    end)

(* ************************************************************************ *)
(* Call translation                                                         *)
(* ************************************************************************ *)

exception Translate_call_exn of varinfo

(* Extended integer types (e.g. int8_t, uint_least16_t, int_fast32_t)
   do not have their own character modifiers, but instead use macros that are
   converted into "standard" modifiers (e.g. "%hhd", "%hu", "%d", etc.).
   Therefore, we cannot enforce their types the same way as for e.g. size_t,
   which has its own modifier. We weaken the check, allowing a different name
   but still requiring same size and signedness. *)
let extended_integer_typenames =
  ["int8_t"; "uint8_t"; "int_least8_t"; "uint_least8_t";
   "int_fast8_t"; "uint_fast8_t";
   "int16_t"; "uint16_t"; "int_least16_t"; "uint_least16_t";
   "int_fast16_t"; "uint_fast16_t";
   "int32_t"; "uint32_t"; "int_least32_t"; "uint_least32_t";
   "int_fast32_t"; "uint_fast32_t";
   "int64_t"; "uint64_t"; "int_least64_t"; "uint_least64_t";
   "int_fast64_t"; "uint_fast64_t"]

let is_extended_integer_type t =
  match t with
  | TNamed (ti, _) -> List.mem ti.tname extended_integer_typenames
  | _ -> false

let integral_rep ikind =
  Cil.bitsSizeOfInt ikind, Cil.isSigned ikind

let expose t =
  Cil.type_remove_attributes_for_c_cast (Cil.unrollType t)

(* From most permissive to least permissive *)
type castability = Strict      (* strictly allowed by the C standard *)
                 | Tolerated   (* tolerated in practice *)
                 | NonPortable (* non-portable minor deviation *)
                 | NonStrict   (* only allowed in non-strict mode *)
                 | Never       (* never allowed *)

let can_cast given expected =
  match expose given, expose expected with
  | t1, t2 when Cil_datatype.Typ.equal t1 t2 -> Strict
  | (TInt (i1,a1) | TEnum({ekind=i1},a1)),
    (TInt (i2,a2) | TEnum({ekind=i2},a2)) ->
    if integral_rep i1 <> integral_rep i2 ||
       not (Cil_datatype.Attributes.equal a1 a2) then
      Never
    else if is_extended_integer_type given then
      Tolerated
    else if i1 = i2 then
      NonPortable
    else
      NonStrict
  | TPtr _, TPtr _ -> Strict
  | _, _ -> Never

let does_fit exp typ =
  match Cil.constFoldToInt exp, Cil.unrollType typ with
  | Some i, (TInt (ekind,_) | TEnum({ekind},_)) ->
    Cil.fitsInInt ekind i
  | _ -> false

(* Variant of [pp_typ] which details the underlying type for enums *)
let pretty_typ fmt t =
  match Cil.unrollType t with
  | TEnum (ei, _) ->
    Format.fprintf fmt "%a (%a)" Printer.pp_typ t
      Printer.pp_typ (TInt (ei.ekind, []))
  | _ -> Printer.pp_typ fmt t

(* cast the i-th argument exp to paramtyp *)
let cast_arg i paramtyp exp =
  let argtyp = Cil.typeOf exp in
  if not (does_fit exp paramtyp) then
    begin match can_cast argtyp paramtyp with
      | Strict | Tolerated -> ()
      | (NonPortable | NonStrict) when not (Strict.get ()) -> ()
      | NonPortable ->
        Self.warning ~current:true ~wkey:wkey_typing
          "Possible portability issues with enum type for argument %d \
           (use -variadic-no-strict to avoid this warning)."
          (i + 1)
      | NonStrict | Never ->
        Self.warning ~current:true ~wkey:wkey_typing
          "Incorrect type for argument %d. \
           The argument will be cast from %a to %a."
          (i + 1)
          pretty_typ argtyp pretty_typ paramtyp
    end;
  Cil.mkCast ~force:false ~newt:paramtyp exp


(* cast a list of args to the tparams list of types and remove unused args *)
let match_args ~callee tparams args =
  (* Remove unused arguments *)
  let paramcount = List.length tparams
  and argcount = List.length args in
  if argcount > paramcount  then
    Self.warning ~current:true ~wkey:wkey_typing
      "Too many arguments: expected %d, given %d. \
       Superfluous arguments will be removed."
      paramcount argcount
  else if argcount < paramcount then (
    Self.warning ~current:true ~wkey:wkey_typing
      "Not enough arguments: expected %d, given %d."
      paramcount argcount;
    raise (Translate_call_exn callee)
  );

  (* Translate params *)
  let new_args, unused_args = List.break paramcount args in
  List.mapi2 cast_arg tparams new_args, unused_args


(* translate a call by applying argument matching/pruning and changing
   callee *)
let match_call ~loc ~fundec scope mk_call new_callee new_tparams args =
  let new_args, unused_args = match_args ~callee:new_callee new_tparams args in
  let call = mk_call (Cil.evar ~loc new_callee) new_args in
  let reads =
    List.map (fun e -> Cil.mkPureExprInstr ~fundec ~scope e) unused_args
  in
  reads @ [call]

(* ************************************************************************ *)
(* Fallback calls                                                           *)
(* ************************************************************************ *)

let fallback_fun_call ~callee loc mk_call vf args =
  let build_fallback_fun ~vf args =
    let module Build =
      Cil_builder.Stateful (struct let loc = vf.vf_decl.vdecl end)
    in

    (* Choose function name *)
    let name = callee.vname in
    let vorig_name = callee.vorig_name in
    let count =
      try Fallback_counts.find name
      with Not_found -> 0
    in
    let count = count + 1 in
    Fallback_counts.replace name count;
    let new_name = name ^ "_fallback_" ^ (string_of_int count) in

    (* Start building the function *)
    let funvar = Build.open_function ~vorig_name new_name in

    (* Set function return type and attributes *)
    let ret_typ, params, _, attrs = Cil.splitFunctionType vf.vf_original_type in
    Build.set_return_type' ret_typ;
    List.iter Build.add_attribute attrs;
    Build.add_stdlib_generated ();

    (* Add parameters *)
    let fixed_params_count = Typ.params_count vf.vf_original_type in
    let add_static_param (name,typ,attributes) =
      ignore (Build.parameter ~attributes typ name)
    and add_variadic_param i e =
      let typ = Cil.typeOf e in
      ignore (Build.parameter typ ("param" ^ string_of_int i))
    in
    List.iter add_static_param (Option.get params);
    List.iteri add_variadic_param (List.drop fixed_params_count args);

    (* Build the default behaviour *)
    let glob = Build.finish_declaration ~register:false () in
    glob, Build.cil_varinfo funvar
  in

  (* Create the new callee *)
  let glob, new_callee = build_fallback_fun ~vf args in
  new_globals := glob :: !new_globals;

  (* Store the translation *)
  Replacements.add new_callee vf.vf_decl;

  (* Translate the call *)
  Self.result ~current:true ~level:2
    "Fallback translation of call %s to a call to the specialized version %s."
    vf.vf_decl.vorig_name new_callee.vname;
  let call = mk_call (Cil.evar ~loc new_callee) args in
  [call]

(* ************************************************************************ *)
(* Aggregator calls                                                         *)
(* ************************************************************************ *)

let find_null exp_list =
  List.ifind (fun e -> Cil.isZero (Cil.constFold false e)) exp_list


let aggregator_call ~fundec ~ghost aggregator scope loc mk_call vf args =
  let {a_target; a_pos; a_type; a_param} = aggregator in
  let name = vf.vf_decl.vorig_name
  and tparams = Typ.params_types a_target.vtype
  and pname, ptyp = a_param in

  (* Check argument count *)
  let argcount = List.length args
  and paramcount = List.length tparams in
  if argcount < paramcount then begin
    Self.warning ~current:true ~wkey:wkey_typing
      "Not enough arguments: expected %d, given %d."
      paramcount argcount;
    raise (Translate_call_exn vf.vf_decl);
  end;

  (* Compute the size of the aggregation *)
  let size = match a_type with
    | EndedByNull ->
      begin try
          find_null (List.drop a_pos args) + 1
        with Not_found ->
          Self.warning ~current:true
            "Failed to find a sentinel (NULL pointer) in the argument list.";
          raise (Translate_call_exn vf.vf_decl);
      end
  in

  (* Convert arguments *)
  let tparams_left = List.take a_pos tparams in
  let tparams_right = List.drop (a_pos + 1) tparams in
  let new_tparams = tparams_left @ List.make size ptyp @ tparams_right in
  let new_args, unused_args = match_args ~callee:vf.vf_decl new_tparams args in

  (* Split the arguments *)
  let args_left, args_rem = List.break a_pos new_args in
  let args_middle, args_right = List.break size args_rem in

  (* Create the call code  *)
  Self.result ~current:true ~level:2
    "Translating call to %s to a call to %s."
    name a_target.vorig_name;
  let pname = if pname = "" then "param" else pname in

  let module Build = Cil_builder.Stateful (struct let loc = loc end) in
  Build.open_block ~into:fundec ~ghost ();
  let init = match args_middle with (* C standard forbids arrays of size 0 *)
    | [] -> [Build.of_init (Cil.makeZeroInit ~loc ptyp)]
    | l -> List.map Build.of_exp l
  in
  let size = List.length init in
  let vaggr = Build.(local (array ~size (of_ctyp ptyp)) pname ~init) in
  let new_args = args_left @ [Build.(cil_exp ~loc (addr vaggr))] @ args_right in
  let new_args,_ = match_args ~callee:vf.vf_decl tparams new_args in
  Build.(List.iter pure (List.map of_exp unused_args));
  Build.of_instr (mk_call (Cil.evar ~loc a_target) new_args);
  Build.finish_instr_list ~scope ()


(* ************************************************************************ *)
(* Overloads calls                                                          *)
(* ************************************************************************ *)

let rec check_arg_matching expected given =
  match Cil.unrollType given, Cil.unrollType expected with
  | (TInt _ | TEnum _), (TInt _ | TEnum _) -> true
  | TPtr _, _ when Cil.isVoidPtrType expected -> true
  | TPtr (t1, _), TPtr (t2, _) -> check_arg_matching t1 t2
  | _, _ -> not (Cil.need_cast given expected)


let rec check_call_matching tparams targs =
  match tparams, targs with
  | [], [] -> true
  | [], _
  (* too many args: this is allowed by the standard (the extra arguments
     are ignored), but in practice this leads to disambiguation issues in
     some cases (e.g. last argument is 0 instead of NULL), so we prefer to
     be strict *)
  (* Not enough input args *)
  | _, [] -> false
  | a1 :: l1, a2 :: l2 ->
    check_arg_matching a1 a2 &&
    check_call_matching l1 l2


let filter_matching_prototypes overload args =
  (* Find suitable candidates for this call *)
  let targs = List.map Cil.typeOf args in
  let check (tparams, _vi) = check_call_matching tparams targs in
  List.filter check overload


let overloaded_call ~fundec overload block loc mk_call vf args =
  let name = vf.vf_decl.vorig_name in

  (* Find the matching prototype *)
  let tparams, new_callee =
    match filter_matching_prototypes overload args with
    | [] -> (* No matching prototype *)
      Self.warning ~current:true ~wkey:wkey_prototype
        "@[No matching prototype found for this call to %s.@.\
         Expected candidates:@.\
         @[<v>       %a@]@.\
         Given arguments:@.\
         @[<v>       %a@]"
        name (pp_overload name) overload
        (pp_prototype name) (List.map Cil.typeOf args);
      raise (Translate_call_exn vf.vf_decl);
    | [(tparams,vi)] -> (* Exactly one matching prototype *)
      tparams, vi
    | l -> (* Several matching prototypes *)
      Self.warning ~current:true ~wkey:wkey_prototype
        "Ambiguous call to %s. Matching candidates are: \
         %a"
        name
        (pp_overload name) l;
      raise (Translate_call_exn vf.vf_decl);
  in

  (* Store the translation *)
  Replacements.add new_callee vf.vf_decl;

  (* Rebuild the call *)
  Self.result ~current:true ~level:2
    "Translating call to the specialized version %a."
    (pp_prototype name) tparams;
  match_call ~loc ~fundec block mk_call new_callee tparams args



(* ************************************************************************ *)
(* Format functions calls                                                   *)
(* ************************************************************************ *)

(* --- Specification building --- *)

let rec static_string a = match a.enode with
  | Const (CStr s) -> Some (Format_string.String s)
  | Const (CWStr s) -> Some (Format_string.WString s)
  | CastE (_, e) -> static_string e
  | _ -> None

let find_global env name =
  try
    Some (Environment.find_global env name)
  with Not_found ->
    Self.warning ~once:true ~wkey:wkey_libc_framac
      "Unable to locate global %s which should be in the Frama-C LibC. \
       Correct specifications can't be generated."
      name;
    None

let find_predicate name =
  match Logic_env.find_all_logic_functions name with
  | f :: _q -> f (* TODO: should we warn in case of overloading? *)
  | [] ->
    Self.warning ~once:true ~wkey:wkey_libc_framac
      "Unable to locate ACSL predicate %s which should be in the Frama-C LibC. \
       Correct specifications can't be generated."
      name;
    raise Not_found

let find_field env structname fieldname =
  try
    let compinfo = Environment.find_struct env structname in
    Cil.getCompField compinfo fieldname
  with Not_found ->
    Self.warning ~once:true
      "Unable to locate %s field %s."
      structname fieldname;
    raise Not_found

let find_predicate_by_width typ narrow_name wide_name =
  match Cil.unrollTypeDeep typ with
  | TPtr (TInt(IChar, _), _) -> find_predicate narrow_name
  | TPtr (t, _) when
      (* drop attributes to remove 'const' qualifiers and fc_stdlib attributes *)
      Cil_datatype.Typ.equal
        (Cil.typeDeepDropAllAttributes (Cil.unrollTypeDeep t))
        Cil.theMachine.Cil.wcharType ->
    find_predicate wide_name
  | _ ->
    Self.warning ~current:true ~wkey:wkey_typing
      "expected single/wide character pointer type, got %a (%a, unrolled %a)"
      Printer.pp_typ typ Cil_types_debug.pp_typ typ Cil_types_debug.pp_typ (Cil.unrollTypeDeep typ);
    raise Not_found

let valid_read_string typ =
  find_predicate_by_width typ "valid_read_string" "valid_read_wstring"

let valid_read_nstring typ =
  find_predicate_by_width typ "valid_read_nstring" "valid_read_nwstring"

let format_length typ =
  find_predicate_by_width typ "format_length" "wformat_length"


let build_specialized_fun env vf format_fun tvparams =
  let open Format_types in
  let module Build =
    Cil_builder.Stateful (struct let loc = vf.vf_decl.vdecl end)
  in

  (* Choose function name *)
  let name = vf.vf_decl.vorig_name in
  vf.vf_specialization_count <- vf.vf_specialization_count + 1;
  let new_name = name ^ "_va_" ^ (string_of_int vf.vf_specialization_count) in

  (* Start building the function *)
  let funvar = Build.open_function ~vorig_name:name new_name in

  (* Set function return type and attributes *)
  let ret_typ, params, _, attrs = Cil.splitFunctionType vf.vf_original_type in
  Build.set_return_type' ret_typ;
  List.iter Build.add_attribute attrs;
  Build.add_stdlib_generated ();

  (* Add parameters *)
  let fresh_param_name =
    let counter = ref 0 in
    fun () ->
      let p = "param" ^ string_of_int !counter in
      incr counter;
      p
  in
  let add_static_param (name,typ,attributes) =
    (* create a new name for parameters which does not have one *)
    let name = if name = "" then fresh_param_name () else name in
    Build.parameter ~attributes typ name
  and add_variadic_param (typ,_dir) =
    let typ = if Cil.isIntegralType typ then
        Cil.integralPromotion typ
      else
        typ
    in
    Build.parameter typ (fresh_param_name ())
  in
  let sformals = List.map add_static_param (Option.get params)
  and vformals = List.map add_variadic_param tvparams
  in


  (* Spec *)
  let sources = ref [] and dests = ref [] in
  let add_source ?(indirect=false) s =
    let s = (s :> Build.source) in
    sources := (if indirect then Build.indirect s else s) :: !sources
  and add_dest d =
    dests := (d :> Build.exp) :: !dests
  in
  (* Add the lval to the list of sources/dests *)
  let add_lval ~indirect lval = function
    | (`ArgIn | `ArgInArray _) -> add_source ~indirect lval
    | (`ArgOut | `ArgOutArray) -> add_dest lval
    | `ArgInOut -> add_source ~indirect lval; add_dest lval
  in
  let add_var ?pos ~indirect (v : Build.var) dir =
    let ty = Build.cil_typeof v in
    (* Use the appropriate logical lval *)
    let lval = match dir with
      | `ArgIn -> (v :> Build.lval)
      | (`ArgInArray _ | `ArgOutArray) -> Build.(index v whole_right)
      | (`ArgOut | `ArgInOut) -> Build.(mem v)
    in
    add_lval ~indirect lval dir;
    (* Build requires/ensures *)
    try match dir with
      | `ArgInArray None ->
        Build.(requires (app (valid_read_string ty) [here] [v]))

      | `ArgInArray (Some precision) ->
        let nterm = match precision with
          | PStar ->
            let size_arg = List.nth vformals (Option.get pos - 1) in
            Build.(cast integer size_arg)
          | PInt n ->
            Build.of_int n
        in
        Build.(requires (app (valid_read_nstring ty) [here] [(v :> Build.exp) ; nterm]))

      | `ArgOut ->
        Build.(requires (valid v));
        Build.(ensures (initialized v))

      | _ -> ()
    with Not_found -> () (* Predicate not found *)
  in


  (* Build variadic parameter source/dest list *)
  let l = List.combine vformals tvparams in
  List.iteri (fun pos (v,(_,dir)) -> add_var ~indirect:false ~pos v dir) l;

  (* Add format source and additional parameters *)
  let fmt = List.nth sformals format_fun.f_format_pos in
  add_var ~indirect:true fmt (`ArgInArray None);

  (* Add buffer source/dest *)
  let add_stream v =
    (* assigns stream->__fc_FILE_data
         \from stream->__fc_FILE_data, __fc_FILE_id *)
    try
      let f_data = find_field env "__fc_FILE" "__fc_FILE_data"
      and f_id = find_field env "__fc_FILE" "__fc_FILE_id" in
      add_lval ~indirect:false Build.(field v f_data) `ArgInOut;
      add_lval ~indirect:true Build.(field v f_id) `ArgIn
    with Not_found ->
      add_var ~indirect:false v `ArgInOut
  in

  (* Add a bounded buffer *)
  let add_buffer buffer size =
    add_var ~indirect:true size `ArgIn;
    (* this is an snprintf-like function; compute and add its precondition:
       \valid(s + (0..n-1)) || \valid(s + (0..format_length(format)-1)) *)
    let valid_range length =
      Build.(valid (buffer + (zero -- (length - one))))
    in
    let left_pred = valid_range size in
    try
      let flen = format_length (Build.cil_typeof buffer) in
      let right_pred = Build.(valid_range (app flen [here] [fmt])) in
      Build.(requires (logor left_pred right_pred))
    with
    | Not_found -> Build.requires left_pred
    | Build.NotAFunction li ->
      Self.abort ~current:true
        "%a should be a logic function, not a predicate"
        Printer.pp_logic_var li.l_var_info
  in

  begin match format_fun.f_buffer, format_fun.f_kind with
    | StdIO, ScanfLike ->
      begin match find_global env "__fc_stdin" with
        | Some vi -> add_stream (Build.var vi)
        | None -> ()
      end
    | StdIO, PrintfLike ->
      begin match find_global env "__fc_stdout" with
        | Some vi -> add_stream (Build.var vi)
        | None -> ()
      end
    | Arg (i, _), ScanfLike ->
      add_var ~indirect:true (List.nth sformals i) (`ArgInArray None)
    | Arg (i, size_pos), PrintfLike ->
      add_var ~indirect:true (List.nth sformals i) (`ArgOutArray);
      begin match size_pos with
        | Some n ->
          add_buffer (List.nth sformals i) (List.nth sformals n)
        | None -> ()
      end
    | Stream i, _ ->
      add_stream (List.nth sformals i)
    | File i, _ ->
      let file = List.nth sformals i in
      add_var ~indirect:true file `ArgIn;
    | Syslog, _ -> ()
  end;

  (* assign \result \from indirect:sources *)
  if not (Cil.isVoidType ret_typ) then
    Build.(assigns [result] (List.map indirect !sources));
  (* assigns dests \from sources *)
  Build.assigns !dests !sources;

  (* Build the default behaviour *)
  let glob = Build.finish_declaration ~register:false () in
  glob, Build.cil_varinfo funvar


(* --- Call translation --- *)

let format_of_ikind = function
  | IBool -> Some `hh, `u
  | IChar -> None, `c
  | ISChar -> Some `hh, `d
  | IUChar -> Some `hh, `u
  | IInt -> None, `d
  | IUInt -> None, `u
  | IShort -> Some `h, `d
  | IUShort -> Some `h, `u
  | ILong -> Some `l, `d
  | IULong -> Some `l, `u
  | ILongLong -> Some `ll, `d
  | IULongLong -> Some `ll, `u

let format_of_fkind k = function
  | FFloat -> None, `f
  | FDouble ->
    (match k with
     | Format_types.PrintfLike -> None, `f
     | ScanfLike -> Some `l, `f)
  | FLongDouble -> Some `L, `f

let rec format_of_type vf k t =
  match t with
  | TInt (ikind,_) | TEnum ({ekind = ikind},_) -> format_of_ikind ikind
  | TFloat (fkind,_) -> format_of_fkind k fkind
  | TPtr(_,_) ->
    (* technically, we might still want to write/read the actual pointer,
       but this is not the most likely possibility. *)
    if Cil.isCharPtrType t then
      None, `s
    else
      None, `p
  | TNamed ({tname;ttype},_) ->
    (match tname with
     | "size_t" -> Some `z, `u
     | "ptrdiff_t" -> Some `t, `d
     | "intmax_t" -> Some `j, `d
     | "uintmax_t" -> Some `j, `u
     (* not really standard, but that's what glibc does. *)
     | "ssize_t" -> Some `z, `d
     | _ -> format_of_type vf k ttype
    )
  (* in the case of a scanf-like function, it might happen
     that we pass a void* whose actual type is coherent with
     the format string itself, but this can't really be checked
     here.
  *)
  | TVoid _ -> raise (Translate_call_exn vf.vf_decl)

  (* these cases should not happen anyway *)
  | TComp _
  | TFun _
  | TArray _
  | TBuiltin_va_list _ -> raise (Translate_call_exn vf.vf_decl)

let infer_format_from_args vf format_fun args =
  let args = List.drop (format_fun.f_format_pos + 1) args in
  let f_format (l,s) =
    Format_types.(
      Specification
        { f_flags = [];
          f_field_width = None;
          f_precision = None;
          f_length_modifier = l;
          f_conversion_specifier = s;
          f_capitalize = false;
        })
  in
  let s_format (l,s) =
    Format_types.(
      Specification
        { s_assignment_suppression = false;
          s_field_width = None;
          s_length_modifier = l;
          s_conversion_specifier = s;
        }
    )
  in
  let treat_one_arg arg =
    let t = Cil.typeOf arg in
    let t =
      match format_fun.f_kind with
      | PrintfLike -> t
      | ScanfLike ->
        if not (Cil.isPointerType t) then begin
          let source = fst arg.eloc in
          Self.warning ~source ~wkey:wkey_typing
            "Expecting pointer as parameter of scanf function. \
             Argument %a has type %a"
            Printer.pp_exp arg Printer.pp_typ t;
          raise (Translate_call_exn vf.vf_decl);
        end;
        Cil.typeOf_pointed t
    in
    format_of_type vf format_fun.f_kind t
  in
  let format = List.map treat_one_arg args in
  match format_fun.f_kind with
  | PrintfLike -> Format_types.FFormat (List.map f_format format)
  | ScanfLike -> Format_types.SFormat (List.map s_format format)

let format_fun_call ~fundec env format_fun scope loc mk_call vf args =
  (* Extract the format if possible *)
  let format =
    try
      let format_arg = List.nth args format_fun.f_format_pos in
      match static_string format_arg with
      | None ->
        Self.warning ~current:true
          "Call to function %s with non-static format argument: \
           assuming that parameters are coherent with the format, and that \
           no %%n specifiers are present in the actual string."
          vf.vf_decl.vorig_name;
        infer_format_from_args vf format_fun args
      | Some s -> Format_parser.parse_format format_fun.f_kind s
    with
    | Format_parser.Invalid_format -> raise (Translate_call_exn vf.vf_decl)
  in

  (* Try to type expected parameters if possible *)
  let find_typedef = Environment.find_type env in
  let tvparams =
    try
      Format_typer.type_format ~find_typedef format
    with Format_typer.Type_not_found type_name ->
      Self.warning ~current:true
        "Unable to find type %s in the source code which should be used in \
         this call:@ no specification will be generated.@ \
         Note that due to cleanup, the type may have been defined in the \
         original code but not used anywhere."
        type_name;
      raise (Translate_call_exn vf.vf_decl)
  in

  (* Create the new callee *)
  let glob, new_callee = build_specialized_fun env vf format_fun tvparams in
  new_globals := glob :: !new_globals;

  (* Store the translation *)
  Replacements.add new_callee vf.vf_decl;

  (* Translate the call *)
  Self.result ~current:true ~level:2
    "Translating call to %s to a call to the specialized version %s."
    vf.vf_decl.vorig_name new_callee.vname;
  let tparams = Typ.params_types new_callee.vtype in
  match_call ~loc ~fundec scope mk_call new_callee tparams args
