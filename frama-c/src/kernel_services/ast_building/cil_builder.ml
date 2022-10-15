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

let unknown_loc = Cil_datatype.Location.unknown


(* --- Types --- *)

module Type =
struct
  exception NotACType

  type ('value,'shape) morphology =
    | Single : ('value,'value) morphology
    | Listed : ('value,'shape) typ -> ('value,'shape list) morphology

  and ('value,'shape) typ = ('value,'shape) morphology * Cil_types.logic_type

  open Cil_types

  (* Logic types *)

  let of_ltyp t = Single, t
  let integer = Single, Linteger
  let real = Single, Lreal

  (* C base types *)

  let of_ctyp t = Single, Ctype t
  let void = Single, Ctype (TVoid [])
  let bool = Single, Ctype (TInt (IBool, []))
  let char = Single, Ctype (TInt (IChar, []))
  let schar = Single, Ctype (TInt (ISChar, []))
  let uchar = Single, Ctype (TInt (IUChar, []))
  let int = Single, Ctype (TInt (IInt, []))
  let unit = Single, Ctype (TInt (IUInt, []))
  let short = Single, Ctype (TInt (IShort, []))
  let ushort = Single, Ctype (TInt (IUShort, []))
  let long = Single, Ctype (TInt (ILong, []))
  let ulong = Single, Ctype (TInt (IULong, []))
  let longlong = Single, Ctype (TInt (ILongLong, []))
  let ulonglong = Single, Ctype (TInt (IULongLong, []))
  let float = Single, Ctype (TFloat (FFloat, []))
  let double = Single, Ctype (TFloat (FDouble, []))
  let longdouble = Single, Ctype (TFloat (FLongDouble, []))

  let ptr = function
    | _, Ctype t -> Single, Ctype (TPtr (t, []))
    | _, _ -> raise NotACType

  let array ?size = function
    | (_,Ctype t) as typ ->
      let to_exp = Cil.integer ~loc:unknown_loc in
      let size = Option.map to_exp size in
      Listed typ,
      Ctype (TArray (t, size, []))
    | _, _ -> raise NotACType


  (* Attrbutes *)

  let attribute (s,t) name params =
    let add_to = Cil.addAttribute (Attr (name, params)) in
    let t = match t with
      | Ctype t -> t
      | _ -> raise NotACType
    in
    let t = match t with
      | TVoid l -> TVoid (add_to l)
      | TInt (kind, l) -> TInt (kind, add_to l)
      | TFloat (kind, l) -> TFloat (kind, add_to l)
      | TPtr (typ, l) -> TPtr (typ, add_to l)
      | TArray (typ, size, l) -> TArray (typ, size, add_to l)
      | TFun (typ, args, variadic, l) -> TFun (typ, args, variadic, add_to l)
      | TNamed (typeinfo, l) -> TNamed (typeinfo, add_to l)
      | TComp (compinfo, l) -> TComp (compinfo, add_to l)
      | TEnum (enuminfo, l) -> TEnum (enuminfo, add_to l)
      | TBuiltin_va_list l -> TBuiltin_va_list (add_to l)
    in
    (s,Ctype t)

  let const typ = attribute typ "const" []
  let stdlib_generated typ = attribute typ "fc_stdlib_generated" []


  (* Conversion *)

  let cil_typ = function
    | _, Ctype ty -> ty
    | _, _ -> raise NotACType

  let cil_logic_type (_,t) = t
end


(* --- C & Logic expressions builder --- *)

module Exp =
struct
  include Type

  (*
    This module exports polymorphic variant to simulate subtyping.
    It uses regular variant internally though, instead of using only the
    polymorphic variant, as
    1. it simplifies greatly the .mli since most of the types don't have
       to be exposed ; it also greatly simplifies mistyping errors for the user
    2. recursive polymorphic variants do not allow inclusion of one into another
    3. it is much easier to type the program with regular variants
  *)

  type label = Cil_types.logic_label

  type const' =
    | Int of int
    | Integer of Integer.t
    | CilConstant of Cil_types.constant
  and var' =
    Cil_types.varinfo
  and lval' =
    | CilLval of Cil_types.lval
    | Var of var'
    | Result
    | Mem of exp'
    | Index of lval' * exp'
    | Field of lval' * Cil_types.fieldinfo
    | FieldNamed of lval' * string
  and exp' =
    | CilExp of Cil_types.exp
    | CilExpCopy of Cil_types.exp
    | CilTerm of Cil_types.term
    | Lval of lval'
    | Const of const'
    | Range of exp' option * exp' option
    | Unop of Cil_types.unop * exp'
    | Binop of Cil_types.binop * exp' * exp'
    | Cast of Cil_types.logic_type * exp'
    | Addr of lval'
    | App of Cil_types.logic_info * label list * exp' list
    | Pred of pred'
  and pred' =
    | ObjectPointer of label * exp'
    | Valid of label * exp'
    | ValidRead of label * exp'
    | Initialized of label * exp'
    | Dangling of label * exp'
    | Allocable of label * exp'
    | Freeable of label * exp'
    | Fresh of label * label * exp' * exp'
  and init' =
    | CilInit of Cil_types.init
    | SingleInit of exp'
    | CompoundInit of Cil_types.typ * init' list

  type const = [ `const of const' ]
  type var = [ `var of var' ]
  type lval = [  var | `lval of lval' ]
  type exp = [ const | lval | `exp of exp' ]
  type init = [ exp | `init of init']

  (* Pretty printing *)

  let rec pretty_const fmt = function
    | Int i -> Format.pp_print_int fmt i
    | Integer i -> Integer.pretty fmt i
    | CilConstant c -> Printer.pp_constant fmt c
  and pretty_var fmt v =
    Printer.pp_varinfo fmt v
  and pretty_lval fmt = function
    | CilLval lv -> Printer.pp_lval fmt lv
    | Var v -> pretty_var fmt v
    | Result -> Format.fprintf fmt "%s" "\result"
    | Mem e -> Format.fprintf fmt "*(%a)" pretty_exp e
    | Index (lv,e) -> Format.fprintf fmt "%a[%a]" pretty_lval lv pretty_exp e
    | Field (lv,fi) ->
      Format.fprintf fmt "%a.%s" pretty_lval lv fi.Cil_types.fname
    | FieldNamed (lv,s) -> Format.fprintf fmt "%a.%s" pretty_lval lv s
  and pretty_exp fmt = function
    | CilExp e -> Printer.pp_exp fmt e
    | CilExpCopy e -> Printer.pp_exp fmt e
    | CilTerm t -> Printer.pp_term fmt t
    | Lval lv -> pretty_lval fmt lv
    | Const c -> pretty_const fmt c
    | Range (o1,o2) ->
      Format.fprintf fmt "(%a .. %a)" pretty_exp_opt o1 pretty_exp_opt o2
    | Unop (op,e) -> Format.fprintf fmt "%a%a" Printer.pp_unop op pretty_exp e
    | Binop (op,e1,e2) ->
      Format.fprintf fmt "(%a %a %a)"
        pretty_exp e1
        Printer.pp_binop op
        pretty_exp e2
    | Cast (lty, e) ->
      Format.fprintf fmt "(%a)%a" Printer.pp_logic_type lty pretty_exp e
    | Addr lv -> Format.fprintf fmt "&%a" pretty_lval lv
    | App (li,labels,args) -> pretty_app fmt (li.l_var_info.lv_name,labels,args)
    | Pred pred ->
      pretty_pred fmt pred
  and pretty_exp_opt fmt o =
    Option.iter (pretty_exp fmt) o
  and pretty_app fmt (name,labels,args) =
    Format.fprintf fmt "%s{%a}(%a)"
      name
      (Pretty_utils.pp_list ~sep:",@ " Printer.pp_logic_label) labels
      (Pretty_utils.pp_list ~sep:",@ " pretty_exp) args
  and pretty_pred fmt = function
    | ObjectPointer (l,e) -> pretty_app fmt ("object_pointer",[l],[e])
    | Valid (l,e) -> pretty_app fmt ("valid",[l],[e])
    | ValidRead (l,e) -> pretty_app fmt ("valid_read",[l],[e])
    | Initialized (l,e) -> pretty_app fmt ("initialized",[l],[e])
    | Dangling (l,e) -> pretty_app fmt ("dangling",[l],[e])
    | Allocable (l,e) -> pretty_app fmt ("allocable",[l],[e])
    | Freeable (l,e) -> pretty_app fmt ("freeable",[l],[e])
    | Fresh (l1,l2,e1,e2) -> pretty_app fmt ("fresh",[l1;l2],[e1;e2])
  and pretty_init fmt = function
    | CilInit init -> Printer.pp_init fmt init
    | SingleInit e -> pretty_exp fmt e
    | CompoundInit (_,l) ->
      Format.fprintf fmt "{%a}" (Pretty_utils.pp_list ~sep:",@ " pretty_init) l

  let pretty fmt = function
    | `none -> ()
    | `const c -> pretty_const fmt c
    | `var v -> pretty_var fmt v
    | `lval lv -> pretty_lval fmt lv
    | `exp e -> pretty_exp fmt e
    | `init i -> pretty_init fmt i

  (* Depolymorphize *)

  let harden_const c =
    match (c :> const) with
    | `const const -> const

  let harden_var v =
    match (v :> var) with
    | `var var -> var

  let harden_lval lv =
    match (lv :> lval) with
    | #var as var -> Var (harden_var var)
    | `lval lval -> lval

  let harden_lval_opt = function
    | `none -> None
    | #lval as lval -> Some (harden_lval lval)

  let harden_exp e =
    match (e :> exp) with
    | #const as const -> Const (harden_const const)
    | #lval as lval -> Lval (harden_lval lval)
    | `exp exp -> exp

  let harden_exp_opt = function
    | `none -> None
    | #exp as exp -> Some (harden_exp exp)

  let harden_exp_list l =
    List.map harden_exp l

  let harden_init i =
    match (i :> init) with
    | #exp as exp -> SingleInit (harden_exp exp)
    | `init init -> init

  (* None *)

  let none = `none

  (* Labels *)

  let here = Cil_types.(BuiltinLabel Here)
  let old = Cil_types.(BuiltinLabel Old)
  let pre = Cil_types.(BuiltinLabel Pre)
  let post = Cil_types.(BuiltinLabel Post)
  let loop_entry = Cil_types.(BuiltinLabel LoopEntry)
  let loop_current = Cil_types.(BuiltinLabel LoopCurrent)
  let program_init = Cil_types.(BuiltinLabel Init)

  (* Constants *)

  let of_constant c = `const (CilConstant c)
  let of_integer i = `const (Integer i)
  let of_int i = `const (Int i)
  let zero = of_int 0
  let one = of_int 1

  (* Lvalues *)

  let var v = `var v
  let of_lval lv = `lval (CilLval lv)

  (* Expressions *)

  let of_exp e = `exp (CilExp e)
  let of_exp_copy e = `exp (CilExpCopy e)
  let unop op e = `exp (Unop (op, harden_exp e))
  let neg e = unop Cil_types.Neg e
  let lognot e = unop Cil_types.LNot e
  let bwnot e = unop Cil_types.BNot e
  let binop op e1 e2 = `exp (Binop (op, harden_exp e1, harden_exp e2))
  let add e1 e2 = binop Cil_types.PlusA e1 e2
  let succ e = add e one
  let add_int e i = add e (of_int i)
  let sub e1 e2 = binop Cil_types.MinusA e1 e2
  let mul e1 e2 = binop Cil_types.Mult e1 e2
  let div e1 e2 = binop Cil_types.Div e1 e2
  let modulo e1 e2 = binop Cil_types.Mod e1 e2
  let shiftl e1 e2 = binop Cil_types.Shiftlt e1 e2
  let shiftr e1 e2 = binop Cil_types.Shiftrt e1 e2
  let lt e1 e2 = binop Cil_types.Lt e1 e2
  let gt e1 e2 = binop Cil_types.Gt e1 e2
  let le e1 e2 = binop Cil_types.Le e1 e2
  let ge e1 e2 = binop Cil_types.Ge e1 e2
  let eq e1 e2 = binop Cil_types.Eq e1 e2
  let ne e1 e2 = binop Cil_types.Ne e1 e2
  let bwand e1 e2 = binop Cil_types.BAnd e1 e2
  let bwor e1 e2 = binop Cil_types.BOr e1 e2
  let bwxor e1 e2 = binop Cil_types.BXor e1 e2
  let logand e1 e2 = binop Cil_types.LAnd e1 e2
  let logor e1 e2 = binop Cil_types.LOr e1 e2
  let cast' t e = `exp (Cast (Cil_types.Ctype t, harden_exp e))
  let cast (_,t) e = `exp (Cast (t, harden_exp e))
  let addr lv = `exp (Addr (harden_lval lv))
  let mem e = `lval (Mem (harden_exp e))
  let index lv e = `lval (Index (harden_lval lv, harden_exp e))
  let field lv fi = `lval (Field (harden_lval lv, fi))
  let fieldnamed lv s = `lval (FieldNamed (harden_lval lv, s))

  (* Expression lists *)

  exception EmptyList

  let reduce f l =
    match (l :> exp list) with
    | [] -> raise EmptyList
    | h :: t -> List.fold_left f h t

  let logand_list l = reduce logand l
  let logor_list l = reduce logor l

  (* Term specific *)

  let result = `lval Result
  let term t = `exp (CilTerm t)
  let range e1 e2 = `exp (Range (harden_exp_opt e1, harden_exp_opt e2))
  let whole = `exp (Range (None, None))
  let whole_right = `exp (Range (Some (Const (Int 0)), None))
  let app logic_info labels args =
    `exp (App (logic_info, labels, harden_exp_list args))

  let object_pointer ?(at=here) e =
    `exp (Pred (ObjectPointer (at, harden_exp e)))
  let valid ?(at=here) e = `exp (Pred (Valid (at, harden_exp e)))
  let valid_read ?(at=here) e = `exp (Pred (ValidRead (at, harden_exp e)))
  let initialized ?(at=here) e = `exp (Pred (Initialized (at, harden_exp e)))
  let dangling ?(at=here) e = `exp (Pred (Dangling (at, harden_exp e)))
  let allocable ?(at=here) e = `exp (Pred (Allocable (at, harden_exp e)))
  let freeable ?(at=here) e = `exp (Pred (Freeable (at, harden_exp e)))
  let fresh l1 l2 e1 e2 =
    `exp (Pred (Fresh  (l1, l2, harden_exp e1, harden_exp e2)))

  (* Initializations *)

  let of_init i = `init (CilInit i)
  let compound t l = `init (CompoundInit (t, List.map harden_init l))

  let rec values : type a. (init, a) typ -> a -> [> init] =
    fun ty x ->
    match ty with
    | Single, Ctype _ -> x
    | Listed sub, Ctype t-> compound t (List.map (values sub) x)
    | _, _ -> raise NotACType

  (* Operators *)

  let (+), (-), ( * ), (/), (%) = add, sub, mul, div, modulo
  let (<<), (>>) = shiftl, shiftr
  let (<), (>), (<=), (>=), (==), (!=) = lt, gt, le, ge, eq, ne
  let (--) = range

  (* Convert *)

  exception LogicInC of exp
  exception CInLogic of exp
  exception NotATerm of exp
  exception NotAPredicate of exp
  exception NotAFunction of Cil_types.logic_info
  exception Typing_error of string

  let typing_error s =
    raise (Typing_error s)

  let get_field ci s =
    try
      Cil.getCompField ci s
    with Not_found ->
      typing_error ("no field " ^ s ^ " in " ^ ci.Cil_types.cname)


  let rec build_constant = function
    | CilConstant const -> const
    | Int i -> build_constant (Integer (Integer.of_int i))
    | Integer i -> Cil_types.(CInt64 (i, IInt, None))

  and build_lval ~loc = function
    | Result as lv -> raise (LogicInC (`lval lv))
    | CilLval lval -> lval
    | Var v -> Cil_types.(Var v, NoOffset)
    | Mem e ->
      let e' = build_exp ~loc e in
      Cil.mkMem ~addr:e' ~off:Cil_types.NoOffset
    | Index (lv, e) ->
      let (host, offset) as lv' = build_lval ~loc lv
      and e' = build_exp ~loc e in
      begin match Cil.(unrollType (typeOfLval lv')) with
        | TArray _ ->
          let offset' = Cil_types.Index (e', NoOffset) in
          host, Cil.addOffset offset' offset
        | TPtr _ ->
          let base = Cil.new_exp ~loc (Lval lv') in
          let addr = Cil.mkBinOp ~loc Cil_types.PlusPI base e' in
          Cil.mkMem ~addr ~off:Cil_types.NoOffset
        | _ -> typing_error "trying to index an lvalue which is not an array \
                             or a pointer"
      end
    | (Field (lv,_) | FieldNamed (lv,_)) as e ->
      let (host, offset) as lv' = build_lval ~loc lv in
      let host', offset', ci = match Cil.(unrollTypeDeep (typeOfLval lv')) with
        | TComp (ci,_) -> host, offset, ci
        | TPtr (TComp (ci,_),_) ->
          Mem (Cil.new_exp ~loc (Lval lv')), Cil_types.NoOffset, ci
        | _ -> typing_error "trying to get a field of an lvalue which is not \
                             of composite type or pointer to a composite type"
      in
      let f = match e with
        | Field (_lv,f) -> f
        | FieldNamed (_lv,s) -> get_field ci s
        | _ -> assert false
      in
      let offset'' = Cil_types.(Field (f, NoOffset)) in
      host', Cil.addOffset offset'' offset'

  and build_exp ~loc = function
    | CilTerm _ | Range _ | App _ | Pred _ as e -> raise (LogicInC (`exp e))
    | CilExp exp -> exp
    | CilExpCopy exp -> Cil.copy_exp exp
    | Const c->
      Cil.new_exp ~loc (Cil_types.Const (build_constant c))
    | Lval lval ->
      Cil.new_exp ~loc (Cil_types.Lval (build_lval ~loc lval))
    | Unop (op,e) ->
      let e' = build_exp ~loc e in
      let oldt = Cil.typeOf e' in
      let newt = Cil.integralPromotion oldt in
      Cil.(new_exp ~loc (Cil_types.UnOp (op, mkCastT ~oldt ~newt e', oldt)))
    | Binop (op,e1,e2) ->
      let is_pointer_type e =
        Cil.(isPointerType (typeOf e))
      in
      let e1' = build_exp ~loc e1
      and e2' = build_exp ~loc e2 in
      let op' = match op with (* Normalize operation *)
        | PlusA when is_pointer_type e1' -> Cil_types.PlusPI
        | MinusA when is_pointer_type e1' -> Cil_types.MinusPI
        | PlusPI when not (is_pointer_type e1') -> Cil_types.PlusA
        | MinusPI when not (is_pointer_type e1') -> Cil_types.MinusA
        | op -> op
      in
      Cil.mkBinOp ~loc op' e1' e2'
    | Cast (Cil_types.Ctype newt, e) ->
      Cil.mkCast ~force:false ~newt (build_exp ~loc e)
    | Cast _ ->
      raise NotACType
    | Addr lv ->
      Cil.mkAddrOrStartOf ~loc (build_lval ~loc lv)

  let rec build_term_lval ~loc ~restyp = function
    | Result -> Cil_types.(TResult (Option.get restyp), TNoOffset)
    | CilLval _ as lv -> raise (CInLogic (`lval lv))
    | Var v -> Cil_types.(TVar (Cil.cvar_to_lvar v), TNoOffset)
    | Mem t ->
      let t' = build_term ~loc ~restyp t in
      Cil_types.(TMem t', TNoOffset)
    | Index (tlv, t) ->
      let (host, offset) as tlv' = build_term_lval ~loc ~restyp tlv
      and t' = build_term ~loc ~restyp t in
      let lty = Cil.typeOfTermLval tlv' in
      begin match Logic_utils.unroll_type lty with
        | Ctype (TArray _) ->
          let offset' = Cil_types.(TIndex (t', TNoOffset)) in
          host, Logic_const.addTermOffset offset' offset
        | Ctype (TPtr _) ->
          let base = Logic_const.term ~loc (TLval tlv') lty in
          let addr = Logic_const.term ~loc (TBinOp (PlusPI,base,t')) lty in
          TMem addr, TNoOffset
        | _ -> typing_error "trying to index a term lvalue which is not a C \
                             array or a C pointer"
      end
    | (Field (tlv,_) | FieldNamed (tlv,_)) as t ->
      let (host, offset) as tlv' = build_term_lval ~loc ~restyp tlv in
      let lty = match Logic_utils.unroll_type (Cil.typeOfTermLval tlv') with
        | Ctype cty -> Cil_types.Ctype (Cil.unrollTypeDeep cty)
        | lty -> lty
      in
      let host', offset', ci = match lty with
        | Ctype (TComp (ci,_)) -> host, offset, ci
        | Ctype (TPtr (TComp (ci,_),_)) ->
          TMem (Logic_const.term ~loc (Cil_types.TLval tlv') lty), TNoOffset, ci
        | _ -> typing_error "trying to get a field of an lvalue which is not \
                             of composite type or pointer to a composite type"
      in
      let f = match t with
        | Field (_lv,f) -> f
        | FieldNamed (_lv,s) -> get_field ci s
        | _ -> assert false
      in
      let offset'' = Cil_types.(TField (f, TNoOffset)) in
      host', Logic_const.addTermOffset offset'' offset'

  and build_term ~loc ~restyp = function
    | Const (CilConstant _) | CilExp _ | CilExpCopy _ as e ->
      raise (CInLogic (`exp e))
    | Pred _ as e ->
      raise (NotATerm (`exp e))
    | CilTerm term -> term
    | Const (Int i) ->
      Logic_const.tinteger ~loc i
    | Const (Integer i) ->
      Logic_const.tint ~loc i
    | Lval lval ->
      let tlval = build_term_lval ~loc ~restyp lval in
      Logic_const.term ~loc Cil_types.(TLval tlval) (Cil.typeOfTermLval tlval)
    | Unop (op,t) ->
      let t' = build_term t ~loc ~restyp in
      let ty = t'.Cil_types.term_type in
      (* TODO: type conversion *)
      Logic_const.term ~loc Cil_types.(TUnOp (op,t')) ty
    | Binop (op,t1,t2) ->
      let t1' = build_term ~loc ~restyp t1
      and t2' = build_term ~loc ~restyp t2 in
      let ty = t1'.Cil_types.term_type in
      let op' = match op with (* Normalize operation *)
        | PlusA when Logic_utils.isLogicPointer t1' -> Cil_types.PlusPI
        | MinusA when Logic_utils.isLogicPointer t1' -> Cil_types.MinusPI
        | PlusPI when not (Logic_utils.isLogicPointer t1') -> Cil_types.PlusA
        | MinusPI when not (Logic_utils.isLogicPointer t1') -> Cil_types.MinusA
        | op -> op
      in
      (* TODO: type conversion *)
      Logic_const.term ~loc Cil_types.(TBinOp (op',t1',t2')) ty
    | Cast (Ctype ct, t) ->
      let t' = build_term ~loc ~restyp t in
      Logic_utils.mk_cast ~loc ct t'
    | Cast (ty, t) ->
      let t' = build_term ~loc ~restyp t in
      Logic_utils.numeric_coerce ty t'
    | Addr lval ->
      let tlval = build_term_lval ~loc ~restyp lval in
      let ty = Cil.typeOfTermLval tlval in
      Logic_utils.mk_logic_AddrOf ~loc tlval ty
    | Range (t1,t2) ->
      let t1' = Option.map (build_term ~loc ~restyp) t1
      and t2' = Option.map (build_term ~loc ~restyp) t2 in
      Logic_const.trange ~loc (t1',t2')
    | App (logic_info, labels, args) ->
      let ty = match logic_info.l_type with
        | None -> raise (NotAFunction logic_info)
        | Some ty -> ty
      in
      let args' = List.map (build_term ~loc ~restyp) args in
      Logic_const.term ~loc (Tapp (logic_info, labels, args')) ty

  and build_relation e = function
    | Cil_types.Lt -> Cil_types.Rlt
    | Cil_types.Gt -> Cil_types.Rgt
    | Cil_types.Le -> Cil_types.Rle
    | Cil_types.Ge -> Cil_types.Rge
    | Cil_types.Eq -> Cil_types.Req
    | Cil_types.Ne -> Cil_types.Rneq
    | _ -> raise (NotAPredicate (`exp e))

  and build_pred_node ~loc ~restyp = function
    | Unop (Cil_types.LNot, p) ->
      let p' = build_pred ~loc ~restyp p in
      Cil_types.Pnot p'
    | Binop (Cil_types.LAnd, p1, p2) ->
      let p1' = build_pred ~loc ~restyp p1
      and p2' = build_pred ~loc ~restyp p2 in
      Cil_types.Pand (p1',p2')
    | Binop (Cil_types.LOr, p1, p2) ->
      let p1' = build_pred ~loc ~restyp p1
      and p2' = build_pred ~loc ~restyp p2 in
      Cil_types.Por (p1',p2')
    | Binop (binop, t1, t2) as e ->
      let rel = build_relation e binop
      and t1' = build_term ~loc ~restyp t1
      and t2' = build_term ~loc ~restyp t2 in
      Cil_types.Prel (rel, t1', t2')
    | Const _ | CilExp _ | CilExpCopy _  | CilTerm _
    | Lval _ | Unop _ | Cast _ | Addr _ | Range _ as e ->
      raise (NotAPredicate (`exp e))
    | App (logic_info, labels, args) ->
      let args' = List.map (build_term ~loc ~restyp) args in
      Cil_types.Papp (logic_info, labels, args')
    | Pred (ObjectPointer (l, t)) ->
      Cil_types.Pobject_pointer (l, build_term ~loc ~restyp t)
    | Pred (Valid (l, t)) ->
      Cil_types.Pvalid (l, build_term ~loc ~restyp t)
    | Pred (ValidRead (l, t)) ->
      Cil_types.Pvalid_read (l, build_term ~loc ~restyp t)
    | Pred (Initialized (l, t)) ->
      Cil_types.Pinitialized (l, build_term ~loc ~restyp t)
    | Pred (Dangling (l, t)) ->
      Cil_types.Pdangling (l, build_term ~loc ~restyp t)
    | Pred (Allocable (l, t)) ->
      Cil_types.Pallocable (l, build_term ~loc ~restyp t)
    | Pred (Freeable (l, t)) ->
      Cil_types.Pfreeable (l, build_term ~loc ~restyp t)
    | Pred (Fresh (l1, l2, t1, t2)) ->
      let t1' = build_term ~loc ~restyp t1
      and t2' = build_term ~loc ~restyp t2 in
      Cil_types.Pfresh (l1, l2, t1', t2')

  and build_pred ~loc ~restyp t =
    Logic_const.unamed ~loc (build_pred_node ~loc ~restyp t)

  let rec build_init ~loc = function
    | CilInit init -> init
    | SingleInit e ->
      Cil_types.SingleInit (build_exp ~loc e)
    | CompoundInit (typ,l) ->
      let index i = Cil_types.(Index (Cil.integer ~loc i, NoOffset)) in
      let initl = List.mapi (fun i sub -> index i, build_init ~loc sub) l in
      Cil_types.CompoundInit (typ, initl)


  (* Export *)

  let cil_logic_label label = label
  let cil_varinfo v = harden_var v
  let cil_constant c = build_constant (harden_const c)
  let cil_lval ~loc lv = build_lval ~loc (harden_lval lv)
  let cil_lval_opt ~loc lv =
    Option.map (build_lval ~loc) (harden_lval_opt lv)
  let cil_exp ~loc e = build_exp ~loc (harden_exp e)
  let cil_exp_opt ~loc e = Option.map (build_exp ~loc) (harden_exp_opt e)
  let cil_exp_list ~loc l = List.map (cil_exp ~loc) l
  let cil_term_lval ~loc ?restyp lv =
    build_term_lval ~loc ~restyp (harden_lval lv)
  let cil_term ~loc ?restyp e = build_term ~loc ~restyp (harden_exp e)
  let cil_iterm ~loc ?restyp e =
    Logic_const.new_identified_term (cil_term ~loc ?restyp e)
  let cil_pred ~loc ?restyp e = build_pred ~loc ~restyp (harden_exp e)
  let cil_ipred ~loc ?restyp e =
    Logic_const.new_predicate (cil_pred ~loc ?restyp e)
  let cil_init ~loc i = build_init ~loc (harden_init i)

  let cil_typeof (`var vi) = vi.Cil_types.vtype
end


(* --- Pure builder --- *)

module Pure =
struct
  include Exp

  type instr' =
    | CilInstr of Cil_types.instr
    | Skip
    | Assign of lval' * exp'
    | Call of lval' option * exp' * exp' list

  type stmt' =
    | CilStmt of Cil_types.stmt
    | CilStmtkind of Cil_types.stmtkind
    | Instr of instr'
    | Sequence of stmt' list
    | Ghost of stmt'

  type instr = [ `instr of instr' ]
  type stmt = [ instr | `stmt of stmt' ]

  (* Sequences *)

  let flatten_sequences l =
    let rec add_one acc = function
      | Sequence l -> add_list acc l
      | stmt -> stmt :: acc
    and add_list acc l =
      List.fold_left add_one acc l
    in
    List.rev (add_list [] l)

  (* Depolymorphize *)

  let harden_instr i =
    match (i :> instr) with
    | `instr instr -> instr

  let harden_stmt s =
    match (s :> stmt) with
    | #instr as instr -> Instr (harden_instr instr)
    | `stmt stmt -> stmt

  (* Build *)

  let of_instr i = `instr (CilInstr i)
  let skip = `instr Skip
  let assign dest src = `instr (Assign (harden_lval dest, harden_exp src))
  let incr dest = `instr (Assign (harden_lval dest, harden_exp (add dest one)))
  let call res callee args =
    `instr (Call (harden_lval_opt res, harden_exp callee, harden_exp_list args))

  let of_stmtkind sk = `stmt (CilStmtkind sk)
  let of_stmt s = `stmt (CilStmt s)
  let of_stmts l = `stmt (Sequence (List.map (fun s -> CilStmt s) l))
  let block l = `stmt (Sequence (List.map harden_stmt l))
  let ghost s = `stmt (Ghost (harden_stmt s))


  (* Convert *)

  let build_instr ~loc = function
    | CilInstr i -> i
    | Skip ->
      Cil_types.Skip (loc)
    | Assign (dest,src) ->
      let dest' = build_lval ~loc dest
      and src' = build_exp ~loc src in
      let src' = Cil.mkCast ~newt:(Cil.typeOfLval dest') src' in
      Cil_types.Set (dest', src', loc)
    | Call (dest,callee,args) ->
      let dest' = Option.map (build_lval ~loc) dest
      and callee' = build_exp ~loc callee
      and args' = List.map (build_exp ~loc) args in
      Cil_types.Call (dest', callee', args', loc)

  let rec build_stmtkind ~loc ~ghost = function
    | CilStmt s -> s.Cil_types.skind
    | CilStmtkind sk -> sk
    | Instr i -> Cil_types.Instr (build_instr ~loc i)
    | Sequence l -> Cil_types.Block (build_block ~loc ~ghost l)
    | Ghost s -> Cil_types.Block (build_block ~loc ~ghost:true [s])

  and build_stmt ~loc ~ghost = function
    | CilStmt s -> s
    | Ghost s -> build_stmt ~loc ~ghost:true s
    | stmt -> Cil.mkStmt ~ghost (build_stmtkind ~loc ~ghost stmt)

  and build_block ~loc ~ghost l =
    let bstmts = List.map (build_stmt ~ghost ~loc) (flatten_sequences l) in
    Cil.mkBlock bstmts

  (* Export *)

  let cil_instr ~loc i = build_instr ~loc (harden_instr i)
  let cil_stmtkind ~loc s = build_stmtkind ~loc ~ghost:false (harden_stmt s)
  let cil_stmt ~loc s = build_stmt ~loc ~ghost:false (harden_stmt s)


  (* Operators *)

  let (:=) = assign
  let (+=) lv e = assign lv (add lv e)
  let (-=) lv e = assign lv (sub lv e)
end


(* --- Stateful builder --- *)

let dkey = Kernel.register_category "cil-builder"

exception WrongContext of string

module type T =
sig
  val loc : Cil_types.location
end

module Stateful (Location : T) =
struct
  include Exp

  type stmt =
    | Label of Cil_types.label
    | CilStmt of Cil_types.stmt
    | CilStmtkind of Cil_types.stmtkind
    | CilInstr of Cil_types.instr

  type scope =
    {
      scope_type: scope_type;
      ghost: bool;
      mutable stmts: stmt list; (* In reverse order *)
      mutable vars: Cil_types.varinfo list; (* In reverse order *)
    }
  and scope_type =
    | Block
    | IfThen of {ifthen_exp: Cil_types.exp}
    | IfThenElse of {ifthenelse_exp: Cil_types.exp; then_block: Cil_types.block}
    | Switch of {switch_exp: Cil_types.exp}
    | Function of {fundec: Cil_types.fundec}


  let loc = Location.loc


  (* Conversion to Cil *)

  let build_instr_list l =
    let rev_build_one acc = function
      | Label _ | CilStmt _ | CilStmtkind _ ->
        raise (WrongContext "not convertible to instr")
      | CilInstr instr -> instr :: acc
    in
    List.fold_left rev_build_one [] l

  let build_stmt_list ~ghost l =
    let rev_build_one acc = function
      | Label l ->
        begin match acc with
          | [] -> (* No generated statement to attach the label to *)
            let stmt = Cil.mkEmptyStmt ~ghost ~loc () in
            stmt.Cil_types.labels <- [l];
            stmt :: acc
          | stmt :: _ -> (* There is a statement to attach the label to *)
            stmt.Cil_types.labels <- l :: stmt.Cil_types.labels;
            acc
        end
      | CilStmt stmt ->
        stmt :: acc
      | CilStmtkind sk ->
        Cil.mkStmt ~ghost sk :: acc
      | CilInstr instr ->
        Cil.mkStmt ~ghost (Cil_types.Instr instr) :: acc
    in
    List.fold_left rev_build_one [] l

  let build_block b =
    let block = Cil.mkBlock (build_stmt_list ~ghost:b.ghost b.stmts) in
    block.Cil_types.blocals <- List.rev b.vars;
    block

  let build_stmtkind b =
    let block = build_block b in
    match b.scope_type with
    | Block ->
      Cil_types.Block block
    | IfThen { ifthen_exp } ->
      Cil_types.If (ifthen_exp, block, Cil.mkBlock [], loc)
    | IfThenElse { ifthenelse_exp; then_block } ->
      Cil_types.If (ifthenelse_exp, then_block, block, loc)
    | Switch { switch_exp } ->
      let open Cil_types in
      (* Cases are only allowed in the current block by the case function *)
      let contains_case stmt =
        List.exists (function Case _ -> true | _ -> false) stmt.labels
      in
      let case_stmts = List.filter contains_case block.bstmts in
      Cil_types.Switch (switch_exp, block, case_stmts , loc)
    | Function _ ->
      raise (WrongContext "not convertible to stmtkind")


  (* State management *)

  let owner: Cil_types.fundec option ref = ref None

  let reset_owner () =
    owner := None

  let set_owner o =
    if Option.is_some !owner then
      raise (WrongContext "already in a function");
    owner := Some o

  let get_owner () =
    match !owner with
    | None -> raise (WrongContext "function context not set")
    | Some fundec -> fundec


  let stack : scope list ref = ref []

  let pretty_stack fmt =
    let pretty_stack_type fmt b =
      match b.scope_type with
      | Block -> Format.pp_print_string fmt "block"
      | IfThen _ -> Format.pp_print_string fmt "if-then"
      | IfThenElse _ -> Format.pp_print_string fmt "if-then-else"
      | Switch _ -> Format.pp_print_string fmt "switch"
      | Function _ -> Format.pp_print_string fmt "function"
    in
    Pretty_utils.pp_list ~pre:"[@[" ~sep:";@," ~last:"@]]"
      pretty_stack_type fmt !stack

  let check_empty () =
    if !stack <> [] then
      raise (WrongContext "some contextes have not been closed")

  let check_not_empty () =
    if !stack = [] then
      raise (WrongContext "only a finish_* function can close all contextes")

  let top () =
    match !stack with
    | [] -> raise (WrongContext "not in an opened context")
    | state :: _ -> state

  let push state =
    let parent_ghost = match !stack with
      | [] -> false
      | s :: _ -> s.ghost
    in
    stack := { state  with ghost = parent_ghost || state.ghost } :: !stack;
    Kernel.debug ~dkey "push onto %t" pretty_stack

  let pop () =
    Kernel.debug ~dkey "pop from %t" pretty_stack;
    match !stack with
    | [] -> raise (WrongContext "not in an opened context")
    | hd :: tail ->
      stack := tail;
      hd

  let finish () =
    reset_owner ();
    match !stack with
    | [] -> raise (WrongContext "not in an opened context")
    | [b] -> b
    | _ :: _ :: _ -> raise (WrongContext "all contextes have not been closed")

  let append_stmt b s =
    b.stmts <- s :: b.stmts

  let append_instr b i =
    append_stmt b (CilInstr i)

  let append_local v =
    let fundec = get_owner () and b = top () in
    fundec.Cil_types.slocals <- fundec.Cil_types.slocals @ [v];
    b.vars <- v :: b.vars


  (* Statements *)

  let of_stmt s =
    let b = top () in
    append_stmt b (CilStmt s)

  let of_stmts l =
    List.iter of_stmt l

  let of_stmtkind sk =
    let b = top () in
    append_stmt b (CilStmtkind sk)

  let break () =
    of_stmtkind (Cil_types.Break loc)

  let return exp =
    of_stmtkind (Cil_types.Return (cil_exp_opt ~loc exp, loc))


  (* Blocks *)

  let new_block ?(ghost=false) scope_type = {
    scope_type;
    ghost;
    stmts = [];
    vars = [];
  }

  let extract_ifthen_block b =
    match b.scope_type with
    | IfThen {ifthen_exp} -> ifthen_exp
    | _ -> raise (WrongContext "not in an opened if-then-else context")

  let extract_switch_block b =
    match b.scope_type with
    | Switch {switch_exp} -> switch_exp
    | _ -> raise (WrongContext "not in a opened switch context")

  let extract_function_block b =
    match b.scope_type with
    | Function {fundec} -> fundec
    | _ -> raise (WrongContext "not in a opened function context")

  let open_function ?ghost ?vorig_name name =
    check_empty ();
    let vorig_name = Option.value ~default:name vorig_name in
    let fundec = Cil.emptyFunction vorig_name in
    fundec.svar.vdecl <- loc;
    fundec.svar.vname <- name;
    set_owner fundec;
    push (new_block ?ghost (Function {fundec}));
    `var fundec.Cil_types.svar

  let open_block ?into ?ghost () =
    Option.iter set_owner into;
    push (new_block ?ghost Block)

  let open_ghost ?into () =
    open_block ?into ~ghost:true ()

  let open_switch ?into exp =
    Option.iter set_owner into;
    let switch_exp = cil_exp ~loc exp in
    push (new_block (Switch {switch_exp}))

  let open_if ?into exp =
    Option.iter set_owner into;
    let ifthen_exp = cil_exp ~loc exp in
    push (new_block (IfThen {ifthen_exp}))

  let open_else () =
    let b = pop () in
    let ifthenelse_exp = extract_ifthen_block b in
    let then_block = build_block b in
    push (new_block (IfThenElse {ifthenelse_exp; then_block}))

  let close () =
    let above = pop () in
    check_not_empty ();
    of_stmtkind (build_stmtkind above) (* add the block to the parent *)

  let finish_block () =
    let b = finish () in
    match build_stmtkind b with
    | Cil_types.Block b -> b
    | _ -> raise (WrongContext "not in an opened simple block context")

  let finish_instr_list ?scope () =
    let b = finish () in
    begin match scope, b.vars with
      | None, [] -> () (* Nothing to do *)
      | Some block, vars ->
        block.Cil_types.blocals <- List.rev vars @ block.Cil_types.blocals
      | None, _ :: _ ->
        raise (WrongContext "a scope must be provided to insert local variables")
    end;
    build_instr_list b.stmts

  let finish_stmt () =
    let b = finish () in
    Cil.mkStmt ~ghost:b.ghost (build_stmtkind b)

  let finish_function ?(register=true) () =
    let b = finish () in
    let fundec = extract_function_block b in
    let open Cil_types in
    let vi = fundec.svar and spec = fundec.sspec in
    fundec.sbody <- build_block b;
    vi.vdefined <- true;
    vi.vghost <- b.ghost;
    if register then begin
      Globals.Functions.replace_by_definition spec fundec loc;
      let keepSwitch = Kernel.KeepSwitch.get () in
      Cfg.prepareCFG ~keepSwitch fundec;
      Cfg.cfgFun fundec;
    end;
    GFun (fundec,loc)

  let finish_declaration ?(register=true) () =
    let b = finish () in
    let fundec = extract_function_block b in
    let open Cil_types in
    let vi = fundec.svar and spec = fundec.sspec in
    if b.stmts <> [] then
      raise (WrongContext "there must not be any built statements");
    vi.vdefined <- false;
    vi.vghost <- b.ghost;
    if register then begin
      Globals.Functions.replace_by_declaration spec vi loc;
    end;
    GFunDecl (spec, vi, loc)

  let case exp =
    let b = top () in
    let _ = extract_switch_block b in
    let label = Cil_types.Case (cil_exp ~loc exp, loc) in
    append_stmt b (Label label)


  (* Functions *)

  let get_return_type () =
    let fundec = get_owner () in
    Cil.getReturnType fundec.svar.vtype

  let set_return_type' ty =
    let fundec = get_owner () in
    Cil.setReturnType fundec ty

  let set_return_type ty =
    set_return_type' (cil_typ ty)

  let add_attribute attr =
    let fundec = get_owner () in
    fundec.svar.vattr <- Cil.addAttribute attr fundec.svar.vattr

  let add_new_attribute attr params =
    add_attribute (Cil_types.Attr (attr, params))

  let add_stdlib_generated () =
    add_new_attribute "fc_stdlib_generated" []


  (* Behaviors *)

  let current_behavior () =
    let b = top () in
    let fundec = extract_function_block b in
    match fundec.sspec.spec_behavior with
    | [] ->
      let default_behavior = Cil.mk_behavior () in
      fundec.sspec.spec_behavior <- [default_behavior];
      default_behavior
    | bhv :: _ -> bhv

  type source = [exp | `indirect of exp]

  let indirect src =
    match (src :> source ) with
    | #exp as it | `indirect it -> `indirect it

  let assigns dests sources =
    let open Cil_types in
    let b = current_behavior ()
    and restyp = get_return_type () in
    let map_source src =
      match (src :> source) with
      | #Exp.exp as e ->
        cil_iterm ~loc ~restyp e
      | `indirect e ->
        let t = cil_term ~loc ~restyp e in
        let t' = { t with term_name = "indirect" :: t.term_name } in
        Logic_const.new_identified_term t'
    and map_dest dst =
      cil_iterm ~loc ~restyp dst
    in
    let dests' = List.map map_dest dests
    and sources' = List.map map_source sources in
    let previous = match b.b_assigns with
      | WritesAny -> []
      | Writes l -> l
    and newones = List.map (fun dst -> dst, From sources') dests' in
    b.b_assigns <- Writes (previous @ newones)

  let requires pred =
    let open Cil_types in
    let b = current_behavior ()
    and restyp = get_return_type () in
    b.b_requires <- b.b_requires @ [cil_ipred ~loc ~restyp pred]

  let ensures pred =
    let open Cil_types in
    let b = current_behavior ()
    and restyp = get_return_type () in
    b.b_post_cond <- b.b_post_cond @ [Normal, cil_ipred ~loc ~restyp pred]


  (* Variables *)

  let local' ?(ghost=false) ?init typ name =
    let fundec = get_owner () and b = top () in
    let ghost = ghost || b.ghost in
    let v = Cil.makeLocalVar ~insert:false ~ghost ~loc fundec name typ in
    begin match init with
      | None -> ()
      | Some init ->
        let local_init = Cil_types.AssignInit (cil_init ~loc init) in
        append_instr b (Cil_types.Local_init (v, local_init, loc));
        v.vdefined <- true
    end;
    append_local v;
    `var v

  let local ?ghost ?init ty name =
    let init = Option.map (values ty) init in
    local' ?ghost ?init (cil_typ ty) name

  let local_copy ?(ghost=false) ?(suffix="_tmp") (`var vi) =
    let fundec = get_owner () and b = top () in
    let ghost = ghost || b.ghost in
    let v = Cil.copyVarinfo vi (vi.Cil_types.vname ^ suffix) in
    v.vghost <- v.vghost || ghost;
    Cil.refresh_local_name fundec v;
    append_local v;
    `var v

  let parameter ?(ghost=false) ?(attributes=[]) typ name =
    let fundec = get_owner () and b = top () in
    let ghost = ghost || b.ghost in
    let v = Cil.makeFormalVar ~ghost ~loc fundec name typ in
    v.Cil_types.vattr <- attributes;
    `var v


  (* Instructions *)

  let of_instr i =
    let b = top () in
    append_instr b i

  let assign lval exp =
    let lval' = cil_lval ~loc lval
    and exp' = cil_exp ~loc exp in
    of_instr (Cil_types.Set (lval', exp', loc))

  let incr lval =
    assign lval (add lval (of_int 1))

  let call dest callee args =
    let dest' = cil_lval_opt ~loc dest
    and callee' = cil_exp ~loc callee
    and args' = cil_exp_list ~loc args in
    of_instr (Cil_types.Call (dest', callee', args', loc))

  let pure exp =
    let exp' = cil_exp ~loc exp in
    let `var v = local' (Cil.typeOf exp') "tmp" ~init:(Exp.of_exp exp') in
    v.vdescr <- Some (Format.asprintf "%a" !Cil.pp_exp_ref exp')

  let skip () =
    of_instr (Cil_types.Skip (loc))


  (* Operators *)

  let (:=) = assign
  let (+=) lv e = assign lv (add lv e)
  let (-=) lv e = assign lv (sub lv e)
end
