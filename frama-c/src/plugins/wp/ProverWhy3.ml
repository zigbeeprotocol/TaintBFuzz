(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

let dkey = Wp_parameters.register_category "prover"
let dkey_api = Wp_parameters.register_category "why3_api"

let option_file = LogicBuiltins.create_option
    ~sanitizer:(fun ~driver_dir x -> Filename.concat driver_dir x)
    "why3" "file"

let option_import = LogicBuiltins.create_option
    ~sanitizer:(fun ~driver_dir:_ x -> x)
    "why3" "import"

let option_qual =
  LogicBuiltins.create_option
    ~sanitizer:(fun ~driver_dir:_ x -> x)
    "why3" "qualifier"

let why3_failure msg =
  Pretty_utils.ksfprintf failwith msg

type why3_conf = {
  env : Why3.Env.env ;
  libdir : string ;
  datadir : string ;
}

module Conf = WpContext.Index(struct
    include Datatype.Unit
    type key = unit
    type data = why3_conf
  end)

let get_why3_conf = Conf.memoize
    begin fun () ->
      let config = Why3Provers.config () in
      let main = Why3.Whyconf.get_main config in
      let ld =
        (WpContext.directory () :> string)::
        ((Wp_parameters.Share.get_dir ~mode:`Must_exist "why3") :> string)::
        (Why3.Whyconf.loadpath main) in
      let libdir = Why3.Whyconf.libdir main in
      let datadir = Why3.Whyconf.datadir main in
      { env = Why3.Env.create_env ld ; libdir ; datadir }
    end

type context = {
  mutable th : Why3.Theory.theory_uc;
  conf: why3_conf;
}

type convert = {
  th : Why3.Theory.theory_uc;
  env: Why3.Env.env;
  subst: Why3.Term.term Lang.F.Tmap.t;
  pool: Lang.F.pool;
  polarity: Cvalues.polarity;
  incomplete_types: (string, Why3.Ty.tysymbol) Hashtbl.t;
  incomplete_symbols: (string, Why3.Term.lsymbol) Hashtbl.t;
  mutable convert_for_export: Lang.F.term Lang.F.Tmap.t;
}

(** The reason for the rebuild *)
let specific_equalities: Lang.For_export.specific_equality list ref =
  ref [Vlist.specialize_eq_list]

let add_specific_equality ~for_tau ~mk_new_eq =
  specific_equalities := { for_tau; mk_new_eq }::!specific_equalities

(** get symbols *)

let get_ls ~cnv ~f ~l ~p =
  let th = Why3.Env.read_theory cnv.env f l in
  let ls =
    try
      Why3.Theory.ns_find_ls th.th_export p
    with Not_found ->
      why3_failure "The symbol %a can't be found in %a.%s"
        Why3.Pp.(print_list dot string) p
        Why3.Pp.(print_list dot string) f l
  in
  ls

let get_ts ~cnv ~f ~l ~p =
  let th = Why3.Env.read_theory cnv.env f l in
  let ls =
    try
      Why3.Theory.ns_find_ts th.th_export p
    with Not_found ->
      why3_failure "The type %a can't be found in %a.%s"
        Why3.Pp.(print_list dot string) p
        Why3.Pp.(print_list dot string) f l
  in
  ls


let t_app ~cnv ~f ~l ~p tl =
  Why3.Term.t_app_infer (get_ls ~cnv ~f ~l ~p) tl

let t_app' ~cnv ~f ~l ~p tl ty =
  Why3.Term.t_app (get_ls ~cnv ~f ~l ~p) tl ty

(** fold map list of at least one element *)
let fold_map map fold = function
  | [] -> assert false (* absurd: forbidden by qed  *)
  | a::tl ->
    List.fold_left (fun acc a -> fold acc (map a)) (map a) tl

let empty_context name : context = {
  th = Why3.Theory.create_theory (Why3.Ident.id_fresh name);
  conf = get_why3_conf ();
}

let empty_cnv ?(polarity=`NoPolarity) (ctx:context) : convert = {
  th = ctx.th;
  subst = Lang.F.Tmap.empty;
  pool = Lang.F.pool ();
  env = ctx.conf.env;
  polarity;
  incomplete_symbols = Hashtbl.create 3;
  incomplete_types = Hashtbl.create 3;
  convert_for_export = Lang.F.Tmap.empty;
}


let lfun_name (lfun:Lang.lfun) =
  match lfun with
  | ACSL f -> Qed.Engine.F_call (Lang.logic_id f)
  | CTOR c -> Qed.Engine.F_call (Lang.ctor_id c)
  | Model({m_source=Generated(_,n)}) -> Qed.Engine.F_call n
  | Model({m_source=Extern e}) -> e.Lang.ext_link


let coerce ~cnv sort expected r =
  match sort, expected with
  | Qed.Logic.Bool, Qed.Logic.Prop -> Why3.Term.(t_equ r t_bool_true)
  | Qed.Logic.Int, Qed.Logic.Real ->
    t_app ~cnv ~f:["real"] ~l:"FromInt" ~p:["from_int"] [r]
  | _ -> r

let name_of_adt = function
  | Lang.Mtype a -> a.Lang.ext_link
  | Mrecord(a,_) -> a.Lang.ext_link
  | Comp (c, KValue) -> Lang.comp_id c
  | Comp (c, KInit) -> Lang.comp_init_id c
  | Atype lt -> Lang.type_id lt

let tvar =
  let tvar = Datatype.Int.Hashtbl.create 10 in
  fun i ->
    Datatype.Int.Hashtbl.memo tvar i
      (fun i ->
         let id = Why3.Ident.id_fresh (Printf.sprintf "a%i" i) in
         Why3.Ty.create_tvsymbol id
      )


(** Sharing *)

let shared (_ : Lang.F.term) = false

let shareable e =
  match Lang.F.repr e with
  | Kint _ | Kreal _ | True | False -> false
  | Times _ | Add _ | Mul _ | Div _ | Mod _ -> true
  | Eq _ | Neq _ | Leq _ | Lt _ -> false
  | Aget _ | Aset _ | Rget _ | Rdef _ | Acst _ -> true
  | And _ | Or _ | Not _ | Imply _ | If _ -> false
  | Fun _ -> not (Lang.F.is_prop e)
  | Bvar _ | Fvar _ | Apply _ | Bind _ -> false

let subterms f e =
  match Lang.F.repr e with
  | Rdef fts ->
    begin
      match Lang.F.record_with fts with
      | None -> Lang.F.lc_iter f e
      | Some(a,fts) -> f a ; List.iter (fun (_,e) -> f e) fts
    end
  | _ -> Lang.F.lc_iter f e

(* path splitting *)
let regexp_col = Str.regexp_string ":"
let regexp_com = Str.regexp_string ","
let regexp_dot = Str.regexp_string "."

let cut_path s = Str.split_delim regexp_dot s

let wp_why3_lib library =
  match LogicBuiltins.get_option option_qual ~library with
  | [] -> [library]
  | [ lib ] -> Str.split_delim regexp_dot lib
  | l ->
    let pp_sep fmt () = Format.pp_print_string fmt ", " in
    Wp_parameters.fatal
      "too many bindings for WP-specific Why3 theory file %s:@\n%a"
      library Format.(pp_print_list ~pp_sep pp_print_string) l

(* conversion *)

let rec of_tau ~cnv (t:Lang.F.tau) =
  match t with
  | Prop -> None
  | Bool -> Some Why3.Ty.ty_bool
  | Int -> Some Why3.Ty.ty_int
  | Real -> Some Why3.Ty.ty_real
  | Array(k,v) ->
    let ts = get_ts ~cnv ~f:["map"] ~l:"Map" ~p:["map"] in
    Some (Why3.Ty.ty_app ts [Why3.Opt.get (of_tau ~cnv k); Why3.Opt.get (of_tau ~cnv v)])
  | Data(adt,l) -> begin
      let s = name_of_adt adt in
      let find s =
        try Hashtbl.find cnv.incomplete_types s
        with Not_found ->
          Why3.Theory.(ns_find_ts (get_namespace cnv.th) (cut_path s))
      in
      match find s with
      | ts -> Some (Why3.Ty.ty_app ts (List.map (fun e -> Why3.Opt.get (of_tau ~cnv e)) l))
      | exception Not_found ->
        why3_failure "Can't find type '%s' in why3 namespace" s
    end
  | Tvar i -> Some (Why3.Ty.ty_var (tvar i))
  | Record _ ->
    why3_failure "Type %a not (yet) convertible" Lang.F.pp_tau t

module Literal =
struct

  open Why3

  let const_int (z:Z.t) =
    let k = BigInt.of_string (Z.to_string z) in
    Term.t_const (Constant.int_const k) Ty.ty_int

  let why3_real ty ~radix ~neg ~int ?(frac="") ?exp () =
    let rc = Number.real_literal ~radix ~neg ~int ~frac ~exp in
    Term.t_const (Constant.ConstReal rc) ty

  let const_real ~cnv (q:Q.t) =
    let mk_real_int z =
      let neg = Z.sign z < 0 in
      let int = Z.to_string (Z.abs z) in
      why3_real Why3.Ty.ty_real ~radix:10 ~neg ~int ()
    in
    if Z.equal Z.one q.den
    then mk_real_int q.num
    else
      t_app ~cnv ~f:["real"] ~l:"Real" ~p:["infix /"]
        [mk_real_int q.num;mk_real_int q.den]

  let cfloat_of_tau tau =
    if      Lang.F.Tau.equal tau Cfloat.t32 then Ctypes.Float32
    else if Lang.F.Tau.equal tau Cfloat.t64 then Ctypes.Float64
    else raise Not_found

  let re_float = Str.regexp
      "-?0x\\([0-9a-f]+\\).\\([0-9a-f]+\\)?0*p?\\([+-]?[0-9a-f]+\\)?$"

  let float_literal_from_q ~cnv tau q =
    let use_hex = true in
    let qf = Q.to_float q in
    let f = match cfloat_of_tau tau with
      | Float32 -> Floating_point.round_to_single_precision_float qf
      | Float64 -> qf
    in
    let s = Pretty_utils.to_string (Floating_point.pretty_normal ~use_hex) f in
    let s = String.lowercase_ascii s in
    if Str.string_match re_float s 0 then
      let group n r = try Str.matched_group n r with Not_found -> "" in
      let neg = Q.sign q < 0 in
      let int,frac,exp = (group 1 s), (group 2 s), (group 3 s) in
      let exp = if String.equal exp "" then None else Some exp in
      let ty = Option.get (of_tau ~cnv tau) in
      why3_real ty ~radix:16 ~neg ~int ~frac ?exp ()
    else raise Not_found

  let const_float ~cnv tau (repr:Lang.F.QED.repr) =
    match repr with
    | Fun(f, [x]) when Lang.Fun.(equal f Cfloat.fq32 || equal f Cfloat.fq64) ->
      begin match Lang.F.repr x with
        | Kreal q -> float_literal_from_q ~cnv tau q
        | _ -> raise Not_found
      end
    | _ -> raise Not_found

  let is_float_literal ~cnv tau repr =
    try (ignore (const_float ~cnv tau repr) ; true)
    with Not_found | Why3.Number.NonRepresentableFloat _ -> false

end

let rec full_trigger = function
  | Qed.Engine.TgAny -> false
  | TgVar _ -> true
  | TgGet(a,k) -> full_trigger a && full_trigger k
  | TgSet(a,k,v) -> full_trigger a && full_trigger k && full_trigger v
  | TgFun(_,xs) | TgProp(_,xs) -> List.for_all full_trigger xs

let rec full_triggers = function
  | [] -> []
  | ts :: tgs ->
    match List.filter full_trigger ts with
    | [] -> full_triggers tgs
    | ts -> ts :: full_triggers tgs

let rec of_trigger ~cnv t =
  match t with
  | Qed.Engine.TgAny -> assert false (* absurd: filter by full_triggers *)
  | Qed.Engine.TgVar v -> begin
      try Lang.F.Tmap.find (Lang.F.e_var v) cnv.subst
      with Not_found -> why3_failure "Unbound variable %a" Lang.F.pp_var v
    end
  | Qed.Engine.TgGet(m,k) ->
    t_app ~cnv ~f:["map"] ~l:"Map" ~p:["get"] [of_trigger ~cnv m;of_trigger ~cnv k]
  | TgSet(m,k,v) ->
    t_app ~cnv ~f:["map"] ~l:"Map" ~p:["set"] [of_trigger ~cnv m;of_trigger ~cnv k;of_trigger ~cnv v]
  | TgFun (f,l) -> begin
      match lfun_name f with
      | F_call s ->
        let ls = Why3.Theory.(ns_find_ls (get_namespace cnv.th) (cut_path s)) in
        Why3.Term.t_app_infer ls (List.map (fun e -> of_trigger ~cnv e) l)
      | _ -> why3_failure "can not convert extented calls in triggers"
    end
  | TgProp (f,l) ->
    begin
      match lfun_name f with
      | F_call s ->
        let ls = Why3.Theory.(ns_find_ls (get_namespace cnv.th) (cut_path s)) in
        Why3.Term.t_app_infer ls (List.map (fun e -> of_trigger ~cnv e) l)
      | _ -> why3_failure "can not convert extented calls in triggers"
    end

let rec of_term ~cnv expected t : Why3.Term.term =
  Wp_parameters.debug ~dkey:dkey_api
    "of_term %a %a@."
    Lang.F.Tau.pretty expected Lang.F.pp_term t;
  let sort =
    try Lang.F.typeof t
    with Not_found ->
      why3_failure "@[<hov 2>Untyped term: %a@]" Lang.F.pp_term t
  in
  let ($) f x = f x in
  let r =
    try coerce ~cnv sort expected $ Lang.F.Tmap.find t cnv.subst
    with Not_found ->
    match Lang.F.repr t, sort, expected with
    | (Fvar _, _, _) -> invalid_arg "unbound variable in of_term"
    | (Bvar _, _, _) -> invalid_arg "bound variable in of_term"
    | Bind((Forall|Exists) as q,_,_), _, _ -> begin
        coerce ~cnv Prop expected $
        let why3_vars, t = successive_binders cnv q t in
        let quant = match q with
          | Qed.Logic.Forall -> Why3.Term.Tforall
          | Qed.Logic.Exists -> Why3.Term.Texists
          | _ -> assert false
        in
        Why3.Term.t_quant quant (Why3.Term.t_close_quant why3_vars [] t)
      end
    | True, _, Prop -> Why3.Term.t_true
    | True, _, Bool -> Why3.Term.t_bool_true
    | False, _, Prop -> Why3.Term.t_false
    | False, _, Bool -> Why3.Term.t_bool_false
    | Kint z, Int, _ -> coerce ~cnv sort expected $ Literal.const_int z
    | Kreal q, Real, _ -> coerce ~cnv sort expected $ Literal.const_real ~cnv q
    | repr, t, _ when Literal.is_float_literal ~cnv t repr ->
      coerce ~cnv sort expected $ Literal.const_float ~cnv t repr
    | Times(z,t), Int, _ ->
      coerce ~cnv sort expected $
      t_app ~cnv ~f:["int"] ~l:"Int" ~p:["infix *"] [Literal.const_int z; of_term ~cnv sort t]
    | Times(z,t), Real, _ ->
      coerce ~cnv sort expected $
      t_app ~cnv ~f:["real"] ~l:"Real" ~p:["infix *"]
        [Literal.const_real ~cnv (Q.of_bigint z); of_term ~cnv sort t]
    | Add l, Int, _ ->
      coerce ~cnv sort expected $
      t_app_fold ~f:["int"] ~l:"Int" ~p:["infix +"] ~cnv sort l
    | Add l, Real, _ ->
      coerce ~cnv sort expected $
      t_app_fold ~f:["real"] ~l:"Real" ~p:["infix +"] ~cnv sort l
    | Mul l, Int, _ ->
      coerce ~cnv sort expected $
      t_app_fold ~f:["int"] ~l:"Int" ~p:["infix *"] ~cnv sort l
    | Mul l, Real, _ ->
      coerce ~cnv sort expected $
      t_app_fold ~f:["real"] ~l:"Real" ~p:["infix *"] ~cnv sort l
    | Leq (a,b), _, Prop ->
      int_or_real ~cnv
        ~fint:["int"] ~lint:"Int" ~pint:["infix <="]
        ~freal:["real"] ~lreal:"Real" ~preal:["infix <="]
        a b
    | Div(a,b), Int, _ ->
      coerce ~cnv sort expected $
      t_app ~cnv ~f:["int"] ~l:"ComputerDivision" ~p:["div"]
        [of_term ~cnv sort a; of_term ~cnv sort b]
    | Mod(a,b), Int, _ ->
      coerce ~cnv sort expected $
      t_app ~cnv ~f:["int"] ~l:"ComputerDivision" ~p:["mod"]
        [of_term ~cnv sort a; of_term ~cnv sort b]
    | Div(a,b), Real, _ ->
      coerce ~cnv sort expected $
      t_app ~cnv ~f:["real"] ~l:"Real" ~p:["infix /"]
        [of_term ~cnv sort a; of_term ~cnv sort b]
    | Lt (a,b), _, Prop ->
      int_or_real ~cnv
        ~fint:["int"] ~lint:"Int" ~pint:["infix <"]
        ~freal:["real"] ~lreal:"Real" ~preal:["infix <"]
        a b
    | Leq (a,b), _, Bool ->
      int_or_real ~cnv
        ~fint:(wp_why3_lib "qed") ~lint:"Qed" ~pint:["zleq"]
        ~freal:(wp_why3_lib "qed") ~lreal:"Qed" ~preal:["rleq"]
        a b
    | Lt (a,b), _, Bool ->
      int_or_real ~cnv
        ~fint:(wp_why3_lib "qed") ~lint:"Qed" ~pint:["zlt"]
        ~freal:(wp_why3_lib "qed") ~lreal:"Qed" ~preal:["rlt"]
        a b
    | And l, _, Bool ->
      t_app_fold ~f:["bool"] ~l:"Bool" ~p:["andb"] ~cnv expected l
    | And l, _, Prop ->
      fold_map (of_term ~cnv expected) Why3.Term.t_and l
    | Or l, _, Bool ->
      t_app_fold ~f:["bool"] ~l:"Bool" ~p:["orb"] ~cnv expected l
    | Or l, _, Prop ->
      fold_map (of_term ~cnv expected) Why3.Term.t_or l
    | Not e, _, Bool ->
      let cnv = {cnv with polarity = Cvalues.negate cnv.polarity} in
      t_app ~cnv ~f:["bool"] ~l:"Bool" ~p:["notb"] [of_term ~cnv expected e]
    | Not e, _, Prop ->
      let cnv = {cnv with polarity = Cvalues.negate cnv.polarity} in
      Why3.Term.t_not (of_term ~cnv expected e)
    | Imply (l,e), _, _ ->
      let e = (of_term ~cnv expected) e in
      let cnv' = {cnv with polarity = Cvalues.negate cnv.polarity} in
      let fold acc a =
        let a = of_term ~cnv:cnv' expected a in
        match expected with
        | Prop -> Why3.Term.t_implies a acc
        | _ (* Bool *) ->
          t_app ~cnv:cnv' ~f:["bool"] ~l:"Bool" ~p:["implb"] [a;acc]
      in
      List.fold_left fold e (List.rev l)
    | Eq (a,b), _, Prop -> begin
        match Lang.F.typeof a with
        | Prop | Bool ->
          Why3.Term.t_iff (of_term ~cnv Prop a) (of_term ~cnv Prop b)
        | tau ->
          match List.find (fun spe -> spe.Lang.For_export.for_tau tau) !specific_equalities with
          | spe when cnv.polarity = `Positive -> of_term ~cnv expected (spe.mk_new_eq a b)
          | exception Not_found -> Why3.Term.t_equ (of_term' cnv a) (of_term' cnv b)
          | _                   -> Why3.Term.t_equ (of_term' cnv a) (of_term' cnv b)
      end
    | Neq (a,b), _, Prop ->
      begin
        match Lang.F.typeof a with
        | Prop | Bool ->
          Why3.Term.t_not (Why3.Term.t_iff (of_term ~cnv Prop a) (of_term ~cnv Prop b))
        | tau ->
          match List.find (fun spe -> spe.Lang.For_export.for_tau tau) !specific_equalities with
          | spe when cnv.polarity = `Negative ->
            Why3.Term.t_not (of_term ~cnv expected (spe.mk_new_eq a b))
          | exception Not_found -> Why3.Term.t_neq (of_term' cnv a) (of_term' cnv b)
          | _                   -> Why3.Term.t_neq (of_term' cnv a) (of_term' cnv b)
      end
    | Eq (a,b), _, Bool ->
      t_app ~cnv ~f:(wp_why3_lib "qed") ~l:"Qed" ~p:["eqb"] [of_term' cnv a; of_term' cnv b]
    | Neq (a,b), _, Bool ->
      t_app ~cnv ~f:(wp_why3_lib "qed") ~l:"Qed" ~p:["neqb"] [of_term' cnv a; of_term' cnv b]
    | If(a,b,c), _, _ ->
      let cnv' = {cnv with polarity = `NoPolarity} in
      Why3.Term.t_if (of_term ~cnv:cnv' Prop a) (of_term ~cnv expected b) (of_term ~cnv expected c)
    | Aget(m,k), _, _ -> begin
        coerce ~cnv sort expected $
        let mtau = Lang.F.typeof m in
        let ksort = match mtau with
          | Array(ksort,_) -> ksort
          | _ -> assert false (* absurd: by qed typing *)in
        t_app ~cnv ~f:["map"] ~l:"Map" ~p:["get"] [of_term ~cnv mtau m;of_term ~cnv ksort k]
      end
    | Aset(m,k,v), Array(ksort,vsort), _ ->
      coerce ~cnv sort expected $
      t_app ~cnv ~f:["map"] ~l:"Map" ~p:["set"] [of_term ~cnv sort m;of_term ~cnv ksort k;of_term ~cnv vsort v]
    | Acst(_,v), Array(_,vsort), _ ->
      coerce ~cnv sort expected $
      t_app' ~cnv ~f:["map"] ~l:"Const" ~p:["const"] [of_term ~cnv vsort v] (of_tau ~cnv sort)
    (* Generic *)
    | Fun (f,l), _, _ -> begin
        let t_app ls l r  =
          Why3.Term.t_app ls l r
        in
        let apply_from_ns s l sort =
          let find s =
            try Hashtbl.find cnv.incomplete_symbols s
            with Not_found ->
              Why3.Theory.(ns_find_ls (get_namespace cnv.th) (cut_path s))
          in
          match find s, expected with
          | ls, (Prop | Bool) ->
            coerce ~cnv sort expected $
            t_app ls l (of_tau ~cnv sort)
          | ls, _ ->
            coerce ~cnv sort expected $
            t_app ls l (of_tau ~cnv sort)
          | exception Not_found -> why3_failure "Can't find '%s' in why3 namespace" s
        in
        let apply_from_ns' s l =
          apply_from_ns s (List.map (fun e -> of_term' cnv e) l)
        in
        match lfun_name f, expected with
        | F_call s, _ -> apply_from_ns' s l sort
        | Qed.Engine.F_subst (s, _), _ -> apply_from_ns' s l sort
        | Qed.Engine.F_left s, _ | Qed.Engine.F_assoc s, _ ->
          let rec aux = function
            | [] -> why3_failure "Empty application"
            | [a] -> of_term ~cnv expected a
            | a::l ->
              apply_from_ns s [of_term' cnv a; aux l] sort
          in
          aux l
        | Qed.Engine.F_right s, _ ->
          let rec aux = function
            | [] -> why3_failure "Empty application"
            | [a] -> of_term ~cnv expected a
            | a::l ->
              apply_from_ns s [aux l;of_term' cnv a] sort
          in
          aux (List.rev l)
        | Qed.Engine.F_list (fcons,fnil), _ ->
          let rec aux = function
            | [] -> apply_from_ns fnil [] sort
            | a::l ->
              apply_from_ns fcons [of_term' cnv a;aux l] sort
          in
          aux l
        | Qed.Engine.F_bool_prop (s,_), Bool | Qed.Engine.F_bool_prop (_,s), Prop ->
          apply_from_ns' s l expected
        | Qed.Engine.F_bool_prop (_,_), _ ->
          why3_failure "badly expected type %a for term %a"
            Lang.F.pp_tau expected Lang.F.pp_term t
      end
    | Rget(a, (Cfield(_,KInit) as f)), _ , tau -> begin
        let s = Lang.name_of_field f in
        match Why3.Theory.(ns_find_ls (get_namespace cnv.th) (cut_path s)) with
        | ls ->
          begin match tau with
            | Prop ->
              Why3.Term.t_equ
                (Why3.Term.t_app ls [of_term' cnv a] (Some Why3.Ty.ty_bool))
                (Why3.Term.t_bool_true)
            | _ ->
              Why3.Term.t_app ls [of_term' cnv a] (of_tau ~cnv tau)
          end
        | exception Not_found -> why3_failure "Can't find '%s' in why3 namespace" s
      end

    | Rget(a,f), _ , _ -> begin
        let s = Lang.name_of_field f in
        match Why3.Theory.(ns_find_ls (get_namespace cnv.th) (cut_path s)) with
        | ls -> Why3.Term.t_app ls [of_term' cnv a] (of_tau ~cnv expected)
        | exception Not_found -> why3_failure "Can't find '%s' in why3 namespace" s
      end
    | Rdef(l), Data(Comp (c, k),_) , _ -> begin
        (* l is already sorted by field *)
        let s = match k with
          | KValue -> Lang.comp_id c
          | KInit -> Lang.comp_init_id c
        in
        match Why3.Theory.(ns_find_ls (get_namespace cnv.th) (cut_path s)) with
        | ls ->
          let l = List.map (fun (_,t) -> of_term' cnv t) l in
          Why3.Term.t_app ls l (of_tau ~cnv expected)
        | exception Not_found -> why3_failure "Can't find '%s' in why3 namespace" s
      end
    | (Rdef _, Data ((Mtype _|Mrecord (_, _)|Atype _), _), _)
    | (Rdef _, (Prop|Bool|Int|Real|Tvar _|Array (_, _)), _)
    | (Aset (_, _, _), (Prop|Bool|Int|Real|Tvar _|Record _|Data (_, _)), _)
    | (Neq (_, _), _, (Int|Real|Tvar _|Array (_, _)|Record _|Data (_, _)))
    | (Eq (_, _), _, (Int|Real|Tvar _|Array (_, _)|Record _|Data (_, _)))
    | (Not _, _, (Int|Real|Tvar _|Array (_, _)|Record _|Data (_, _)))
    | (Or _, _, (Int|Real|Tvar _|Array (_, _)|Record _|Data (_, _)))
    | (And _, _, (Int|Real|Tvar _|Array (_, _)|Record _|Data (_, _)))
    | (Lt (_, _), _, (Int|Real|Tvar _|Array (_, _)|Record _|Data (_, _)))
    | (Leq (_, _), _, (Int|Real|Tvar _|Array (_, _)|Record _|Data (_, _)))
    | (Div (_, _), (Prop|Bool|Tvar _|Array (_, _)|Record _|Data (_, _)), _)
    | (Mod (_, _), (Prop|Bool|Real|Tvar _|Array (_, _)|Record _|Data (_, _)), _)
    | (Mul _, (Prop|Bool|Tvar _|Array (_, _)|Record _|Data (_, _)), _)
    | (Add _, (Prop|Bool|Tvar _|Array (_, _)|Record _|Data (_, _)), _)
    | (Times (_, _), (Prop|Bool|Tvar _|Array (_, _)|Record _|Data (_, _)), _)
    | (Kreal _, (Prop|Bool|Int|Tvar _|Array (_, _)|Record _|Data (_, _)), _)
    | (Kint _, (Prop|Bool|Real|Tvar _|Array (_, _)|Record _|Data (_, _)), _)
    | (False, _, (Int|Real|Tvar _|Array (_, _)|Record _|Data (_, _)))
    | (True, _, (Int|Real|Tvar _|Array (_, _)|Record _|Data (_, _)))
    | (Acst (_, _), (Prop|Bool|Int|Real|Tvar _|Record _|Data (_, _)), _)
      -> assert false (* absurd: by typing *)
    | (Bind (Lambda, _, _), _, _)
    | Apply _ , _, _
    | Rdef _, Record _, _ ->
      why3_failure
        "Can't convert to why3 the qed term %a of type %a"
        Lang.F.pp_term t Lang.F.pp_tau sort
  in
  r

and t_app_fold  ~cnv ~f ~l ~p expected lt =
  let fold acc a =
    t_app ~cnv ~f ~l ~p [acc;a]
  in
  fold_map (of_term ~cnv expected) fold lt

and of_term' cnv t =
  of_term ~cnv (Lang.F.typeof t) t

and share cnv expected t =
  let l = Lang.F.QED.shared ~shareable ~shared ~subterms [t] in
  let cnv,lets = mk_lets cnv l in
  let t = of_term ~cnv expected t in
  let t = List.fold_left (fun t (x,e') ->
      Why3.Term.t_let_close x e' t
    ) t lets
  in
  t

and mk_lets cnv l =
  List.fold_left (fun (cnv,lets) e ->
      let cnv' = {cnv with polarity = `NoPolarity} in
      let e' = of_term ~cnv:cnv' (Lang.F.typeof e) e in
      match e'.t_ty with
      | None -> ({cnv with subst = Lang.F.Tmap.add e e' cnv.subst},lets)
      | Some ty ->
        let x = Why3.Ident.id_fresh (Lang.F.basename e) in
        let x = Why3.Term.create_vsymbol x ty in
        (* Format.printf "lets %a = %a : %a@."
         *   Why3.Pretty.print_vsty x
         *   Why3.Pretty.print_term e'
         *   Why3.Pretty.print_ty (Why3.Term.t_type e'); *)
        let cnv = {cnv with subst = Lang.F.Tmap.add e (Why3.Term.t_var x) cnv.subst } in
        let lets = (x,e')::lets in
        cnv,lets
    ) (cnv,[]) l

and successive_binders cnv q t =
  match Lang.F.repr t with
  | Bind((Forall|Exists) as q',tau,t) when q' = q ->
    let x = Lang.F.fresh cnv.pool tau in
    let x' = Why3.Ident.id_fresh (Lang.F.Tau.basename tau) in
    let x' = Why3.Term.create_vsymbol x' (Why3.Opt.get (of_tau ~cnv tau)) in
    let cnv = {cnv with subst = Lang.F.Tmap.add (Lang.F.e_var x) (Why3.Term.t_var x') cnv.subst} in
    let t = Lang.F.QED.e_unbind x t in
    let why3_vars, t = successive_binders cnv q t in
    x'::why3_vars, t
  | _ ->
    [], share cnv Prop t

and int_or_real ~cnv ~fint ~lint ~pint ~freal ~lreal ~preal a b =
  match (Lang.F.typeof a), (Lang.F.typeof b) with
  | Int, Int ->
    t_app_fold ~f:fint ~l:lint ~p:pint ~cnv Int [a; b]
  | Real, Int | Real, Real | Int, Real ->
    t_app_fold ~f:freal ~l:lreal ~p:preal ~cnv Real [a; b]
  | _ -> assert false

let convert cnv expected t =
  (* rewrite terms which normal form inside qed are different from the one of the provers *)
  let t, convert_for_export = Lang.For_export.rebuild ~cache:cnv.convert_for_export t in
  cnv.convert_for_export <- convert_for_export;
  Lang.For_export.in_state (share cnv expected) t

let mk_binders cnv l =
  List.fold_left (fun (cnv,lets) v ->
      match of_tau ~cnv (Lang.F.tau_of_var v) with
      | None -> why3_failure "Quantification on prop"
      | Some ty ->
        let x = Why3.Ident.id_fresh (Lang.F.Var.basename v) in
        let x = Why3.Term.create_vsymbol x ty in
        let e = Lang.F.e_var v in
        let cnv = {cnv with subst = Lang.F.Tmap.add e (Why3.Term.t_var x) cnv.subst } in
        let lets = x::lets in
        cnv,lets
    ) (cnv,[]) (List.rev l)

(** visit definitions and add them in the task *)

module CLUSTERS = WpContext.Index
    (struct
      type key = Definitions.cluster
      type data = int * Why3.Theory.theory
      let name = "ProverWhy3.CLUSTERS"
      let compare = Definitions.cluster_compare
      let pretty = Definitions.pp_cluster
    end)



let filenoext file =
  let basename = Filename.basename file in
  (try Filename.chop_extension basename
   with Invalid_argument _ -> basename)

class visitor (ctx:context) c =
  object(self)

    inherit Definitions.visitor c


    (* --- Files, Theories and Clusters --- *)

    method add_builtin_lib =
      self#add_import_file ["bool"] "Bool" ;
      self#add_import_file ["int"] "Int" ;
      self#add_import_file ["int"] "ComputerDivision" ;
      self#add_import_file ["real"] "RealInfix" ;
      self#on_library "qed";
      self#add_import_file ["map"] "Map"

    method on_cluster c =
      let name = Definitions.cluster_id c in
      Wp_parameters.debug ~dkey:dkey_api "Start on_cluster %s@." name;
      let th_name = String.capitalize_ascii name in
      let thy =
        let age = try fst (CLUSTERS.find c) with Not_found -> (-1) in
        if age < Definitions.cluster_age c then
          let ctx = empty_context th_name in
          let v = new visitor ctx c in
          v#add_builtin_lib;
          v#vself;
          let th = Why3.Theory.close_theory ctx.th in
          if Wp_parameters.has_print_generated () then
            Log.print_on_output
              begin fun fmt ->
                Format.fprintf fmt "---------------------------------------------@\n" ;
                Format.fprintf fmt "--- Context '%s' Cluster '%s' @\n"
                  (WpContext.get_context () |> WpContext.S.id) name;
                Format.fprintf fmt "---------------------------------------------@\n" ;
                Why3.Pretty.print_theory fmt th;
              end ;
          CLUSTERS.update c (Definitions.cluster_age c, th);
          th
        else
          snd (CLUSTERS.find c)
      in
      let th = ctx.th in
      let th = Why3.Theory.open_scope th name in
      let th = Why3.Theory.use_export th thy in
      let th = Why3.Theory.close_scope th ~import:true in
      Wp_parameters.debug ~dkey:dkey_api "End  on_cluster %s@." name;
      ctx.th <- th


    method section _ = ()

    method add_import ?was thy =
      match Str.split_delim regexp_dot thy with
      | [] -> why3_failure "[driver] empty import option"
      | l ->
        let file, thy = Why3.Lists.chop_last l in
        self#add_import_use file thy (Why3.Opt.get_def thy was) ~import:true

    method add_import_file file thy =
      self#add_import_use ~import:true file thy thy

    method add_import_file_as file thy name =
      self#add_import_use ~import:false file thy name

    method add_import_use ~import file thy name =
      Wp_parameters.debug ~dkey:dkey_api
        "@[use@ %s@ @[%a.%s@]@ as@ %s@]"
        (if import then "import" else "")
        Why3.Pp.(print_list (Why3.Pp.constant_string ".") string) file
        thy name ;
      let thy = Why3.Env.read_theory ctx.conf.env file thy in
      let th = ctx.th in
      let th = Why3.Theory.open_scope th name in
      let th = Why3.Theory.use_export th thy in
      let th = Why3.Theory.close_scope th ~import in
      ctx.th <- th

    method on_library thy =
      let copy_file source =
        if not (Datatype.Filepath.equal
                  (Datatype.Filepath.of_string (Filename.dirname source))
                  (Wp_parameters.Share.get_dir "."))
        then
          let tgtdir = WpContext.directory () in
          let why3src = Filename.basename source in
          let target = Printf.sprintf "%s/%s" (tgtdir :> string) why3src in
          Command.copy source target
      in
      let iter_file opt =
        match Str.split_delim regexp_col opt with
        | [file] ->
          let filenoext = filenoext file in
          copy_file file;
          self#add_import_file [filenoext]
            (String.capitalize_ascii filenoext);
        | [file;lib] ->
          copy_file file;
          self#add_import_file [filenoext file] lib;
        | [file;lib;name] ->
          copy_file file;
          self#add_import_file_as [filenoext file] lib name;
        | _ -> why3_failure
                 "[driver] incorrect why3.file %S for library '%s'"
                 opt thy
      in
      let iter_import opt =
        List.iter (fun import ->
            match Str.split_delim regexp_col import with
            | [ th ] -> self#add_import th
            | [ th ; was ] -> self#add_import ~was th
            | _ -> why3_failure
                     "[driver] incorrect why3.import %S for library '%s'"
                     opt thy
          ) (Str.split regexp_com opt)
      in
      begin
        List.iter iter_file
          (LogicBuiltins.get_option option_file ~library:thy) ;
        List.iter iter_import
          (LogicBuiltins.get_option option_import ~library:thy) ;
      end

    method on_type lt def =
      match def with
      | Tabs ->
        let id = Why3.Ident.id_fresh (Lang.type_id lt) in
        let map i _ = tvar i in
        let tv_args = List.mapi map lt.lt_params in
        let id = Why3.Ty.create_tysymbol id tv_args NoDef in
        let decl = Why3.Decl.create_ty_decl id in
        ctx.th <- Why3.Theory.add_decl ~warn:false ctx.th decl;
      | Tdef t ->
        let id = Why3.Ident.id_fresh (Lang.type_id lt) in
        let map i _ = tvar i in
        let tv_args = List.mapi map lt.lt_params in
        let cnv = empty_cnv ctx in
        let t = Why3.Opt.get (of_tau ~cnv t) in
        let id = Why3.Ty.create_tysymbol id tv_args (Alias t) in
        let decl = Why3.Decl.create_ty_decl id in
        ctx.th <- Why3.Theory.add_decl ~warn:false ctx.th decl;
      | Tsum cases ->
        let name = Lang.type_id lt in
        let id = Why3.Ident.id_fresh name in
        let map i _ = tvar i in
        let tv_args = List.mapi map lt.lt_params in
        let tys = Why3.Ty.create_tysymbol id tv_args NoDef in
        let cnv = empty_cnv ctx in
        Hashtbl.add cnv.incomplete_types name tys ;
        let tv_args = List.map Why3.Ty.ty_var tv_args in
        let return_ty = Why3.Ty.ty_app tys tv_args in
        let constr = List.length cases in
        let cases = List.map (fun (c,targs) ->
            let name = match c with | Lang.CTOR c -> Lang.ctor_id c | _ -> assert false in
            let id = Why3.Ident.id_fresh name in
            let targs = List.map (fun t -> Why3.Opt.get (of_tau ~cnv t)) targs in
            let ls = Why3.Term.create_fsymbol ~constr id targs return_ty in
            let proj = List.map (fun _ -> None) targs in
            (ls,proj)
          ) cases in
        let decl = Why3.Decl.create_data_decl [tys,cases] in
        ctx.th <- Why3.Theory.add_decl ~warn:false ctx.th decl;
      | Trec fields ->
        let name = Lang.type_id lt in
        let id = Why3.Ident.id_fresh name in
        let map i _ = tvar i in
        let tv_args = List.mapi map lt.lt_params in
        let tys = Why3.Ty.create_tysymbol id tv_args NoDef in
        let cnv = empty_cnv ctx in
        Hashtbl.add cnv.incomplete_types name tys ;
        let tv_args = List.map Why3.Ty.ty_var tv_args in
        let return_ty = Why3.Ty.ty_app tys tv_args in
        let fields,args = List.split @@ List.map (fun (f,ty) ->
            let name = Lang.name_of_field f in
            let id = Why3.Ident.id_fresh name in
            let ty = Why3.Opt.get (of_tau ~cnv ty) in
            let ls = Why3.Term.create_fsymbol id [return_ty] ty in
            Some ls,ty
          ) fields in
        let id = Why3.Ident.id_fresh (Lang.type_id lt) in
        let cstr = Why3.Term.create_fsymbol ~constr:1 id args return_ty in
        let decl = Why3.Decl.create_data_decl [tys,[cstr,fields]] in
        ctx.th <- Why3.Theory.add_decl ~warn:false ctx.th decl;

    method private on_comp_gen kind c fts =
      begin
        let make_id = match kind with
          | Lang.KValue -> Lang.comp_id
          | Lang.KInit -> Lang.comp_init_id
        in
        let compare_field (f,_) (g,_) =
          let cmp = Lang.Field.compare f g in
          if cmp = 0 then assert false (* by definition *) else cmp
        in
        let fts = Option.map (List.sort compare_field) fts in
        (*TODO:NUPW: manage UNIONS *)
        let id = Why3.Ident.id_fresh (make_id c) in
        let ts = Why3.Ty.create_tysymbol id [] Why3.Ty.NoDef in
        let ty = Why3.Ty.ty_app ts [] in
        let id = Why3.Ident.id_fresh (make_id c) in
        let cnv = empty_cnv ctx in
        let map (f,tau) =
          let ty_ctr = of_tau ~cnv tau in
          let id = Why3.Ident.id_fresh (Lang.name_of_field f) in
          let ls = Why3.Term.create_lsymbol id [ty] ty_ctr in
          (Some ls,Why3.Opt.get ty_ctr)
        in
        let fields = Option.map (List.map map) fts in
        let decl = match fields with
          | None -> Why3.Decl.create_ty_decl ts
          | Some fields ->
            let constr =
              Why3.Term.create_fsymbol ~constr:1 id (List.map snd fields) ty
            in
            Why3.Decl.create_data_decl [ts,[constr,List.map fst fields]]
        in
        ctx.th <- Why3.Theory.add_decl ~warn:false ctx.th decl;
      end

    method on_comp = self#on_comp_gen KValue
    method on_icomp = self#on_comp_gen KInit

    method private make_lemma cnv (l: Definitions.dlemma) =
      let id = Why3.Ident.id_fresh (Lang.lemma_id l.l_name) in
      let id = Why3.Decl.create_prsymbol id in
      List.iter (Lang.F.add_var cnv.pool) l.l_forall;
      let cnv, vars = Lang.For_export.in_state (mk_binders cnv) l.l_forall in
      let t = convert cnv Prop (Lang.F.e_prop l.l_lemma) in
      let triggers = full_triggers l.l_triggers in
      let triggers = Lang.For_export.in_state (List.map (List.map (of_trigger ~cnv))) triggers in
      let t = Why3.Term.t_forall_close vars triggers t in
      id, t

    method on_dlemma l =
      if l.l_kind <> Check then
        let kind = Why3.Decl.(if l.l_kind = Admit then Paxiom else Plemma) in
        let cnv = empty_cnv ctx in
        let id, t = self#make_lemma cnv l in
        let decl = Why3.Decl.create_prop_decl kind id t in
        ctx.th <- Why3.Theory.add_decl ~warn:false ctx.th decl

    method on_dfun d =
      Wp_parameters.debug ~dkey:dkey_api "Define %a@." Lang.Fun.pretty d.d_lfun ;
      let cnv = empty_cnv ctx in
      List.iter (Lang.F.add_var cnv.pool) d.d_params;
      begin
        match d.d_definition with
        | Logic t ->
          let id = Why3.Ident.id_fresh (Qed.Export.link_name (lfun_name d.d_lfun)) in
          let map e = Why3.Opt.get (of_tau ~cnv (Lang.F.tau_of_var e)) in
          let ty_args = List.map map d.d_params in
          let id = Why3.Term.create_lsymbol id ty_args (of_tau ~cnv t) in
          let decl = Why3.Decl.create_param_decl id in
          ctx.th <- Why3.Theory.add_decl ~warn:false ctx.th decl;
        | Function(t,mu,v) -> begin
            match mu with
            | Rec -> (* transform recursive function into an axioms *)
              let name = Qed.Export.link_name (lfun_name d.d_lfun) in
              let id = Why3.Ident.id_fresh name in
              let map e = Why3.Opt.get (of_tau ~cnv (Lang.F.tau_of_var e)) in
              let ty_args = List.map map d.d_params in
              let result = of_tau ~cnv t in
              let id = Why3.Term.create_lsymbol id ty_args result in
              let decl = Why3.Decl.create_param_decl id in
              ctx.th <- Why3.Theory.add_decl ~warn:false ctx.th decl;
              let cnv = empty_cnv ctx in
              List.iter (Lang.F.add_var cnv.pool) d.d_params;
              let cnv, vars = mk_binders cnv d.d_params in
              let t = share cnv t v in
              let t =
                Why3.Term.t_forall_close vars []
                  (Why3.Term.t_equ
                     (Why3.Term.t_app id (List.map Why3.Term.t_var vars) result)
                     t)
              in
              let decl =
                Why3.Decl.create_prop_decl Why3.Decl.Paxiom
                  (Why3.Decl.create_prsymbol (Why3.Ident.id_fresh (name^"_def")))
                  t in
              ctx.th <- Why3.Theory.add_decl ~warn:false ctx.th decl;
            | Def ->
              let id = Why3.Ident.id_fresh (Qed.Export.link_name (lfun_name d.d_lfun)) in
              let map e = Why3.Opt.get (of_tau ~cnv (Lang.F.tau_of_var e)) in
              let ty_args = List.map map d.d_params in
              let result = of_tau ~cnv t in
              let id = Why3.Term.create_lsymbol id ty_args result in
              let cnv, vars = mk_binders cnv d.d_params in
              let t = share cnv t v in
              let decl = Why3.Decl.make_ls_defn id vars t in
              let decl = Why3.Decl.create_logic_decl [decl] in
              ctx.th <- Why3.Theory.add_decl ~warn:false ctx.th decl
          end
        | Predicate(mu,p) -> begin
            match mu with
            | Rec ->
              let name = Qed.Export.link_name (lfun_name d.d_lfun) in
              let id = Why3.Ident.id_fresh name in
              let map e = Why3.Opt.get (of_tau ~cnv (Lang.F.tau_of_var e)) in
              let ty_args = List.map map d.d_params in
              let result = None in
              let id = Why3.Term.create_lsymbol id ty_args result in
              let decl = Why3.Decl.create_param_decl id in
              ctx.th <- Why3.Theory.add_decl ~warn:false ctx.th decl;
              let cnv = empty_cnv ctx in
              List.iter (Lang.F.add_var cnv.pool) d.d_params;
              let cnv, vars = mk_binders cnv d.d_params in
              let t = share cnv Prop (Lang.F.e_prop p) in
              let t =
                Why3.Term.t_forall_close vars []
                  (Why3.Term.t_iff t
                     (Why3.Term.t_app id (List.map Why3.Term.t_var vars) result))
              in
              let decl =
                Why3.Decl.create_prop_decl Why3.Decl.Paxiom
                  (Why3.Decl.create_prsymbol (Why3.Ident.id_fresh (name^"_def")))
                  t in
              ctx.th <- Why3.Theory.add_decl ~warn:false ctx.th decl;
            | Def ->
              let id = Why3.Ident.id_fresh (Qed.Export.link_name (lfun_name d.d_lfun)) in
              let map e = Why3.Opt.get (of_tau ~cnv (Lang.F.tau_of_var e)) in
              let ty_args = List.map map d.d_params in
              let id = Why3.Term.create_lsymbol id ty_args None in
              let cnv, vars = mk_binders cnv d.d_params in
              let t = share cnv Prop (Lang.F.e_prop p) in
              let decl = Why3.Decl.make_ls_defn id vars t in
              let decl = Why3.Decl.create_logic_decl [decl] in
              ctx.th <- Why3.Theory.add_decl ~warn:false ctx.th decl
          end
        | Inductive dl ->
          (* create predicate symbol *)
          let fname = Qed.Export.link_name (lfun_name d.d_lfun) in
          let id = Why3.Ident.id_fresh fname in
          let map e = Why3.Opt.get (of_tau ~cnv (Lang.F.tau_of_var e)) in
          let ty_args = List.map map d.d_params in
          let fid = Why3.Term.create_lsymbol id ty_args None in
          let make_case (l:Definitions.dlemma) =
            let cnv = empty_cnv ctx in
            Hashtbl.add cnv.incomplete_symbols fname fid ;
            self#make_lemma cnv l
          in
          let ind_decl = (fid, List.map make_case dl) in
          ctx.th <- Why3.Theory.add_ind_decl ctx.th Why3.Decl.Ind [ind_decl]
      end

  end

(* -------------------------------------------------------------------------- *)
(* --- Goal Compilation                                                   --- *)
(* -------------------------------------------------------------------------- *)

let goal_id = (Why3.Decl.create_prsymbol (Why3.Ident.id_fresh "wp_goal"))

let prove_goal ~id ~title ~name ?axioms t =
  (* Format.printf "why3_of_qed start@."; *)
  let goal = Definitions.cluster ~id ~title () in
  let ctx = empty_context name in
  let v = new visitor ctx goal in
  Wp_parameters.debug ~dkey:dkey_api "%t"
    begin fun fmt ->
      Format.fprintf fmt "---------------------------------------------@\n" ;
      Format.fprintf fmt "EXPORT GOAL %s@." id ;
      Format.fprintf fmt "PROP @[<hov 2>%a@]@." Lang.F.pp_pred t ;
      Format.fprintf fmt "---------------------------------------------@\n" ;
    end ;
  v#add_builtin_lib;
  v#vgoal axioms t;
  let cnv = empty_cnv ~polarity:`Positive ctx in
  let t = convert cnv Prop (Lang.F.e_prop t) in
  let decl = Why3.Decl.create_prop_decl Pgoal goal_id t in
  let th = Why3.Theory.close_theory ctx.th in
  if Wp_parameters.has_print_generated () then begin
    let th_uc_tmp = Why3.Theory.add_decl ~warn:false ctx.th decl in
    let th_tmp    = Why3.Theory.close_theory th_uc_tmp in
    Wp_parameters.debug ~dkey:Wp_parameters.cat_print_generated "%a"
      Why3.Pretty.print_theory th_tmp
  end;
  th, decl

let prove_prop ?axioms ~pid prop =
  let id = WpPropId.get_propid pid in
  let title = Pretty_utils.to_string WpPropId.pretty pid in
  let name = "WP" in
  let th, decl = prove_goal ?axioms ~id ~title ~name prop in
  let t = None in
  let t = Why3.Task.use_export t th in
  Why3.Task.add_decl t decl

let task_of_wpo wpo =
  let pid = wpo.Wpo.po_pid in
  match wpo.Wpo.po_formula with
  | Wpo.GoalAnnot v ->
    let pid = wpo.Wpo.po_pid in
    let axioms = v.Wpo.VC_Annot.axioms in
    let prop = Wpo.GOAL.compute_proof ~pid v.Wpo.VC_Annot.goal in
    (* Format.printf "Goal: %a@." Lang.F.pp_pred prop; *)
    prove_prop ~pid prop ?axioms
  | Wpo.GoalLemma v ->
    let lemma = v.Wpo.VC_Lemma.lemma in
    let depends = v.Wpo.VC_Lemma.depends in
    let prop = Lang.F.p_forall lemma.l_forall lemma.l_lemma in
    let axioms = Some(lemma.l_cluster,depends) in
    prove_prop ~pid prop ?axioms

(* -------------------------------------------------------------------------- *)
(* --- Prover Task                                                        --- *)
(* -------------------------------------------------------------------------- *)

let prover_task env prover task =
  let config = Why3Provers.config () in
  let prover_config = Why3.Whyconf.get_prover_config config prover in
  let drv = Why3.Whyconf.load_driver (Why3.Whyconf.get_main config)
      env prover_config in
  let remove_for_prover =
    if prover.prover_name = "Alt-Ergo"
    then Filter_axioms.remove_for_altergo
    else Filter_axioms.remove_for_why3
  in
  let trans = Why3.Trans.seq [
      remove_for_prover;
      Filter_axioms.trans;
      Filter_axioms.def_into_axiom
    ] in
  let task =
    if prover.prover_name = "Coq"
    then task
    else Why3.Trans.apply trans task
  in
  drv , prover_config , Why3.Driver.prepare_task drv task

(* -------------------------------------------------------------------------- *)
(* --- Prover Call                                                        --- *)
(* -------------------------------------------------------------------------- *)

let altergo_step_limit = Str.regexp "^Steps limit reached:"

type prover_call = {
  prover : Why3Provers.t ;
  call : Why3.Call_provers.prover_call ;
  steps : int option ;
  timeout : int ;
  mutable timeover : float option ;
  mutable interrupted : bool ;
  mutable killed : bool ;
}

let ping_prover_call ~libdir p =
  match Why3.Call_provers.query_call p.call with
  | NoUpdates
  | ProverStarted ->
    let () =
      if p.timeout > 0 then
        match p.timeover with
        | None ->
          let started = Unix.time () in
          p.timeover <- Some (started +. 2.0 +. float p.timeout)
        | Some timeout ->
          let time = Unix.time () in
          if time > timeout then
            begin
              Wp_parameters.debug ~dkey
                "Hard Kill (late why3server timeout)" ;
              p.interrupted <- true ;
              Why3.Call_provers.interrupt_call ~libdir p.call ;
            end
    in Task.Wait 100
  | InternalFailure exn ->
    let msg = Format.asprintf "@[<hov 2>%a@]"
        Why3.Exn_printer.exn_printer exn in
    Task.Return (Task.Result (VCS.failed msg))
  | ProverInterrupted -> Task.(Return Canceled)
  | ProverFinished _ when p.killed -> Task.(Return Canceled)
  | ProverFinished pr ->
    let r =
      match pr.pr_answer with
      | Timeout -> VCS.timeout (int_of_float pr.pr_time)
      | Valid -> VCS.result ~time:pr.pr_time ~steps:pr.pr_steps VCS.Valid
      | Invalid -> VCS.result ~time:pr.pr_time ~steps:pr.pr_steps VCS.Invalid
      | OutOfMemory -> VCS.failed "out of memory"
      | StepLimitExceeded -> VCS.result ?steps:p.steps VCS.Stepout
      | Unknown _ -> VCS.unknown
      | _ when p.interrupted -> VCS.timeout p.timeout
      | Failure s -> VCS.failed s
      | HighFailure ->
        let alt_ergo_hack =
          p.prover.prover_name = "Alt-Ergo" &&
          Str.string_match altergo_step_limit pr.pr_output 0
        in
        if alt_ergo_hack then VCS.result ?steps:p.steps VCS.Stepout
        else VCS.failed "Unknown error"
    in
    Wp_parameters.debug ~dkey
      "@[@[Why3 result for %a:@] @[%a@] and @[%a@]@."
      Why3.Whyconf.print_prover p.prover
      (Why3.Call_provers.print_prover_result ~json:false) pr
      VCS.pp_result r;
    Task.Return (Task.Result r)

let call_prover_task ~timeout ~steps ~conf prover call =
  let libdir = conf.libdir in
  Wp_parameters.debug ~dkey "Why3 run prover %a with timeout %d, steps %d@."
    Why3.Whyconf.print_prover prover
    (Why3.Opt.get_def (-1) timeout)
    (Why3.Opt.get_def (-1) steps) ;
  let timeout = match timeout with None -> 0 | Some tlimit -> tlimit in
  let pcall = {
    call ; prover ;
    killed = false ;
    interrupted = false ;
    steps ; timeout ; timeover = None ;
  } in
  let ping = function
    | Task.Kill ->
      pcall.killed <- true ;
      Why3.Call_provers.interrupt_call ~libdir call ;
      Task.Yield
    | Task.Coin -> ping_prover_call ~libdir pcall
  in
  Task.async ping

(* -------------------------------------------------------------------------- *)
(* --- Batch Prover                                                       --- *)
(* -------------------------------------------------------------------------- *)

let digest wpo drv prover task =
  let file = Wpo.DISK.file_goal
      ~pid:wpo.Wpo.po_pid
      ~model:wpo.Wpo.po_model
      ~prover:(VCS.Why3 prover) in
  let _ = Command.print_file file
      begin fun fmt ->
        Format.fprintf fmt "(* WP Task for Prover %s *)@\n"
          (Why3Provers.print_why3 prover) ;
        Why3.Driver.print_task_prepared drv fmt task ;
      end
  in Digest.file file |> Digest.to_hex

let batch pconf driver ~conf ?script ~timeout ~steplimit prover task =
  let steps = match steplimit with Some 0 -> None | _ -> steplimit in
  let limit =
    let memlimit = Why3.Whyconf.memlimit (Why3.Whyconf.get_main (Why3Provers.config ())) in
    let def = Why3.Call_provers.empty_limit in
    { Why3.Call_provers.limit_time = Why3.Opt.get_def def.limit_time timeout;
      Why3.Call_provers.limit_steps = Why3.Opt.get_def def.limit_time steps;
      Why3.Call_provers.limit_mem = memlimit;
    } in
  let with_steps = match steps, pconf.Why3.Whyconf.command_steps with
    | None, _ -> false
    | Some _, Some _ -> true
    | Some _, None -> false
  in
  let steps = if with_steps then steps else None in
  let command = Why3.Whyconf.get_complete_command pconf ~with_steps in
  let inplace = if script <> None then Some true else None in
  let call = Why3.Driver.prove_task_prepared ?old:script ?inplace
      ~command ~limit ~libdir:conf.libdir ~datadir:conf.datadir driver task in
  call_prover_task ~conf ~timeout ~steps prover call

(* -------------------------------------------------------------------------- *)
(* --- Interactive Prover (Coq)                                           --- *)
(* -------------------------------------------------------------------------- *)

let editor_mutex = Task.mutex ()

let editor_command pconf =
  let config = Why3Provers.config () in
  try
    let ed = Why3.Whyconf.editor_by_id config pconf.Why3.Whyconf.editor in
    String.concat " " (ed.editor_command :: ed.editor_options)
  with Not_found ->
    Why3.Whyconf.(default_editor (get_main config))

let scriptfile ~force ~ext wpo =
  let dir = Wp_parameters.get_session_dir ~force "interactive" in
  Format.sprintf "%s/%s%s" (dir :> string) wpo.Wpo.po_sid ext

let updatescript ~script driver task =
  let backup = script ^ ".bak" in
  Sys.rename script backup ;
  let old = open_in backup in
  Command.pp_to_file script
    (fun fmt ->
       ignore @@ Why3.Driver.print_task_prepared ~old driver fmt task
    );
  close_in old ;
  let d_old = Digest.file backup in
  let d_new = Digest.file script in
  if String.equal d_new d_old then Extlib.safe_remove backup

let editor ~script ~merge ~conf wpo pconf driver prover task =
  Task.sync editor_mutex
    begin fun () ->
      Wp_parameters.feedback ~ontty:`Transient "Editing %S..." script ;
      Cache.clear_result ~digest:(digest wpo driver) prover task ;
      if merge then updatescript ~script driver task ;
      let command = editor_command pconf in
      let call =
        Why3.Call_provers.call_editor
          ~command ~datadir:conf.datadir ~libdir:conf.libdir script
      in
      call_prover_task ~conf ~timeout:None ~steps:None pconf.prover call
    end

let compile ~script ~timeout ~conf wpo pconf driver prover task =
  let digest = digest wpo driver in
  let runner = batch ~conf pconf driver ~script in
  Cache.get_result ~digest ~runner ~timeout ~steplimit:None prover task

let prepare ~mode wpo driver task =
  let ext = Filename.extension (Why3.Driver.file_of_task driver "S" "T" task) in
  let force = mode <> VCS.Batch in
  let script = scriptfile ~force wpo ~ext in
  if Sys.file_exists script then Some (script, true) else
  if force then
    begin
      Command.pp_to_file script
        (fun fmt ->
           ignore @@ Why3.Driver.print_task_prepared driver fmt task
        );
      Some (script, false)
    end
  else None

let interactive ~mode wpo pconf driver prover task =
  let time = Wp_parameters.InteractiveTimeout.get () in
  let timeout = if time <= 0 then None else Some time in
  let conf = get_why3_conf () in
  match prepare ~mode wpo driver task with
  | None -> Task.return VCS.unknown
  | Some (script, merge) ->
    match mode with
    | VCS.Batch ->
      compile ~script ~timeout ~conf wpo pconf driver prover task
    | VCS.Update ->
      if merge then updatescript ~script driver task ;
      compile ~script ~timeout ~conf wpo pconf driver prover task
    | VCS.Edit ->
      let open Task in
      editor ~script ~merge ~conf wpo pconf driver prover task >>= fun _ ->
      compile ~script ~timeout ~conf wpo pconf driver prover task
    | VCS.Fix ->
      let open Task in
      compile ~script ~timeout ~conf wpo pconf driver prover task >>= fun r ->
      if VCS.is_valid r then return r else
        editor ~script ~merge ~conf wpo pconf driver prover task >>= fun _ ->
        compile ~script ~timeout ~conf wpo pconf driver prover task
    | VCS.FixUpdate ->
      let open Task in
      if merge then updatescript ~script driver task ;
      compile ~script ~timeout ~conf wpo pconf driver prover task >>= fun r ->
      if VCS.is_valid r then return r else
        let merge = false in
        editor ~script ~merge ~conf wpo pconf driver prover task >>= fun _ ->
        compile ~script ~timeout ~conf wpo pconf driver prover task

(* -------------------------------------------------------------------------- *)
(* --- Prove WPO                                                          --- *)
(* -------------------------------------------------------------------------- *)

let is_trivial (t : Why3.Task.task) =
  let goal = Why3.Task.task_goal_fmla t in
  Why3.Term.t_equal goal Why3.Term.t_true

let build_proof_task ?(mode=VCS.Batch) ?timeout ?steplimit ~prover wpo () =
  try
    (* Always generate common task *)
    let context = Wpo.get_context wpo in
    let task = WpContext.on_context context task_of_wpo wpo in
    if Wp_parameters.Generate.get ()
    then Task.return VCS.no_result (* Only generate *)
    else
      let conf = WpContext.on_context context get_why3_conf () in
      let drv , pconf , task = prover_task conf.env prover task in
      if is_trivial task then
        Task.return VCS.valid
      else
      if pconf.interactive then
        interactive ~mode wpo pconf drv prover task
      else
        Cache.get_result
          ~digest:(digest wpo drv)
          ~runner:(batch ~conf pconf drv ?script:None)
          ~timeout ~steplimit prover task
  with exn ->
    if Wp_parameters.has_dkey dkey_api then
      Wp_parameters.fatal "[Why3 Error] %a@\n%s"
        Why3.Exn_printer.exn_printer exn
        Printexc.(raw_backtrace_to_string @@ get_raw_backtrace ())
    else
      Task.failed "[Why3 Error] %a" Why3.Exn_printer.exn_printer exn

let prove ?mode ?timeout ?steplimit ~prover wpo =
  Task.later (build_proof_task ?mode ?timeout ?steplimit ~prover wpo) ()

(* -------------------------------------------------------------------------- *)
