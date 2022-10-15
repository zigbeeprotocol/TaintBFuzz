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

type 'a alarm_gen =
  remove_trivial:bool ->
  on_alarm:(invalid:bool -> Alarms.alarm -> unit) ->
  'a -> unit

type bound_kind = Alarms.bound_kind = Lower_bound | Upper_bound

(* Tries to evaluate expr as a constant value (Int64.t).
   Uses Cil constant folding (e.g. for (-0x7ffffff -1) => Some (-2147483648)) on
   32 bits *)
let get_expr_val expr = Cil.constFoldToInt expr

(* Creates [0 <= e] and [e < size] assertions *)
let valid_index ~remove_trivial ~on_alarm e size =
  let alarm bk =
    let b = match bk with
      | Lower_bound -> None
      | Upper_bound -> Some size
    in
    (* Do not create upper-bound check on GNU zero-length arrays *)
    if not (bk == Upper_bound && Cil.isZero size) then begin
      on_alarm ~invalid:false (Alarms.Index_out_of_bound(e, b))
    end
  in
  if remove_trivial then begin
    (* See if the two assertions do not trivially hold. In this
       case, do not return then *)
    let v_e = get_expr_val e in
    let v_size = get_expr_val size in
    let neg_ok =
      Option.fold ~none:false ~some:(Integer.le Integer.zero) v_e
      || Cil.isUnsignedInteger (Cil.typeOf e)
    in
    if not neg_ok then alarm Lower_bound;
    let pos_ok = match v_e, v_size with
      | Some v_e, Some v_size -> Integer.lt v_e v_size
      | None, _ | _, None -> false
    in
    if not pos_ok then alarm Upper_bound
  end else begin
    alarm Lower_bound;
    alarm Upper_bound;
  end


(* returns the assertion associated with an lvalue:
   returns non empty assertions only on pointer dereferencing and array access.
   The validity assertions are emitted using [valid] if
   [~read_only] is false, or with [valid_read] otherwise *)
let lval_assertion ~read_only ~remove_trivial ~on_alarm lv =
  (* For accesses to known arrays we generate an assertions that constrains
     the index. This is simpler than the [\valid] assertion *)
  let rec check_array_access default off typ in_struct =
    match off with
    | NoOffset ->
      if default then
        on_alarm ~invalid:false (Alarms.Memory_access(lv, read_only))
    | Field (fi, off) ->
      (* Mark that we went through a struct field, then recurse *)
      check_array_access default off fi.ftype true
    | Index (e, off) ->
      match Cil.unrollType typ with
      | TArray (bt, Some size, _) ->
        if Kernel.SafeArrays.get () || not in_struct then begin
          (* Generate an assertion for this access, then go deeper in
             case other accesses exist *)
          valid_index ~remove_trivial ~on_alarm e size;
          check_array_access default off bt in_struct
        end else
          (* Access to an array embedded in a struct with option
             [-unsafe-arrays]. Honor the option and generate only
             the default [\valid] assertion *)
          check_array_access true off bt in_struct
      | TArray (bt, None, _) -> check_array_access true off bt in_struct
      | _ -> assert false
  in
  match lv with
  | Var vi , off -> check_array_access false off vi.vtype false
  | (Mem _ as lh), off ->
    if not (Cil.isFunctionType (Cil.typeOfLval lv)) then
      check_array_access true off (Cil.typeOfLhost lh) false

(* assertion for lvalue initialization *)
let lval_initialized_assertion ~remove_trivial:_ ~on_alarm lv =
  let typ = Cil.typeOfLval lv in
  match lv with
  | Var vi, NoOffset ->
    (* Note: here [lv] has structure/union type or fundamental type.
       We exclude structures and unions. And for fundamental types:
       - globals (initialized and then only written with initialized values)
       - formals (checked at function call)
       - temporary variables (initialized during AST normalization)
    *)
    if not (vi.vglob || vi.vformal || vi.vtemp)
    && not (Cil.isStructOrUnionType typ)
    then
      on_alarm ~invalid:false (Alarms.Uninitialized lv)
  | _ ->
    if not (Cil.isFunctionType typ || Cil.isStructOrUnionType typ) then
      on_alarm ~invalid:false (Alarms.Uninitialized lv)

(* assertion for unary minus signed overflow *)
let uminus_assertion ~remove_trivial ~on_alarm exp =
  (* - expr overflows if exp is TYPE_MIN *)
  let t = Cil.unrollType (Cil.typeOf exp) in
  let size = Cil.bitsSizeOf t in
  let min_ty = Cil.min_signed_number size in
  (* alarm is bound <= exp, hence bound must be MIN_INT+1 *)
  let bound = Integer.add Integer.one min_ty in
  let alarm ?(invalid=false) () =
    let a = Alarms.Overflow(Alarms.Signed, exp, bound, Lower_bound) in
    on_alarm ~invalid a
  in
  if remove_trivial then begin
    match get_expr_val exp with
    | None -> alarm ()
    | Some a64 ->
      (* constant operand *)
      if Integer.equal a64 min_ty then
        alarm ~invalid:true ()
  end
  else alarm ()

(* assertions for multiplication/addition/subtraction overflows *)
let mult_sub_add_assertion ~signed ~remove_trivial ~on_alarm (exp,op,lexp,rexp) =
  (* signed multiplication/addition/subtraction:
     the expression overflows iff its integer value
     is strictly more than [max_ty] or strictly less than [min_ty] *)
  let t = Cil.unrollType (Cil.typeOf exp) in
  let size = Cil.bitsSizeOf t in
  let min_ty, max_ty =
    if signed then Cil.min_signed_number size, Cil.max_signed_number size
    else Integer.zero, Cil.max_unsigned_number size
  in
  let alarm ?(invalid=false) bk =
    let bound = match bk with
      | Upper_bound -> max_ty
      | Lower_bound -> min_ty
    in
    let signed = if signed then Alarms.Signed else Alarms.Unsigned in
    on_alarm ~invalid (Alarms.Overflow (signed, exp, bound, bk));
  in
  let alarms () =
    alarm Lower_bound;
    alarm Upper_bound;
  in
  if remove_trivial then begin
    match get_expr_val lexp, get_expr_val rexp, op with
    | Some l, Some r, _ -> (* both operands are constant *)
      let warn r =
        let warn bk = alarm ~invalid:true bk in
        if Integer.gt r max_ty then warn Upper_bound
        else if Integer.lt r min_ty then warn Lower_bound
      in
      (match op with
       | MinusA -> warn (Integer.sub l r)
       | PlusA -> warn (Integer.add l r)
       | Mult -> warn (Integer.mul l r)
       | _ -> assert false)

    | _, Some v , PlusA | Some v, _, PlusA ->
      if Integer.(gt v zero) then alarm Upper_bound
      else if Integer.(lt v zero) then alarm Lower_bound (* signed only *)

    | _, Some r , MinusA ->
      if Integer.(gt r zero) then alarm Lower_bound
      else if Integer.(lt r zero) then alarm Upper_bound (* signed only *)

    | Some l, None , MinusA ->
      if signed then begin
        (* The possible range for [-r] is [-max_int .. -min_int] i.e.
           [min_int+1..max_int+1]; we need to check [l] w.r.t [-1]. *)
        if Integer.(gt l minus_one) then alarm Upper_bound
        else if Integer.(lt l minus_one) then alarm Lower_bound
      end
      else begin
        (* Only negative overflows are possible, since r is positive. (TODO:
           nothing can happen on [max_int]. *)
        alarm Lower_bound
      end

    | Some v, None, Mult | None, Some v, Mult
      when Integer.is_zero v || Integer.is_one v -> ()

    | None, None, _ | Some _, None, _ | None, Some _, _ -> alarms ()
  end
  else alarms ()

(* assertions for division and modulo (divisor is 0) *)
let divmod_assertion ~remove_trivial ~on_alarm divisor =
  (* division or modulo: overflow occurs when divisor is equal to zero *)
  let alarm ?(invalid=false) () =
    on_alarm ~invalid (Alarms.Division_by_zero divisor);
  in
  if remove_trivial then begin
    match get_expr_val divisor with
    | None -> (* divisor is not a constant *)
      alarm ();
    | Some v64 ->
      if Integer.equal v64 Integer.zero then
        (* divide by 0 *)
        alarm ~invalid:true ()
        (* else divide by constant which is not 0: nothing to assert *)
  end
  else alarm ()

(* assertion for signed division overflow *)
let signed_div_assertion ~remove_trivial ~on_alarm (exp, lexp, rexp) =
  (* Signed division: overflow occurs when dividend is equal to the
     the minimum (negative) value for the signed integer type,
     and divisor is equal to -1. Under the hypothesis (cf Value) that
     integers are represented in two's complement.
     Nothing done for modulo (the result of TYPE_MIN % -1 is 0, which does not
     overflow).
     Still it may be dangerous on a number of compilers / architectures
     (modulo may be performed in parallel with division) *)
  let t = Cil.unrollType (Cil.typeOf rexp) in
  let size = Cil.bitsSizeOf t in
  (* check dividend_expr / divisor_expr : if constants ... *)
  (* compute smallest representable "size bits" (signed) integer *)
  let max_ty = Cil.max_signed_number size in
  let alarm ?(invalid=false) () =
    let a = Alarms.Overflow(Alarms.Signed, exp, max_ty, Alarms.Upper_bound) in
    on_alarm ~invalid a;
  in
  if remove_trivial then begin
    let min = Cil.min_signed_number size in
    match get_expr_val lexp, get_expr_val rexp with
    | Some e1, _ when not (Integer.equal e1 min) ->
      (* dividend is constant, with an unproblematic value *)
      ()
    | _, Some e2 when not (Integer.equal e2 Integer.minus_one) ->
      (* divisor is constant, with an unproblematic value *)
      ()
    | Some _, Some _ ->
      (* invalid constant division *)
      alarm ~invalid:true ()
    | None, Some _ | Some _, None | None, None ->
      (* at least one is not constant: cannot conclude *)
      alarm ()
  end
  else alarm ()

(* Assertions for the left and right operands of left and right shift. *)
let shift_assertion ~remove_trivial ~on_alarm (exp, upper_bound) =
  let alarm ?(invalid=false) () =
    let a = Alarms.Invalid_shift(exp, upper_bound) in
    on_alarm ~invalid a ;
  in
  if remove_trivial then begin
    match get_expr_val exp with
    | None -> alarm ()
    | Some c64 ->
      (* operand is constant:
         check it is nonnegative and strictly less than the upper bound (if
         any) *)
      let upper_bound_ok = match upper_bound with
        | None -> true
        | Some u -> Integer.lt c64 (Integer.of_int u)
      in
      if not (Integer.ge c64 Integer.zero && upper_bound_ok) then
        alarm ~invalid:true ()
  end
  else alarm ()

(* The right operand of shifts should be nonnegative and strictly less than the
   width of the promoted left operand. *)
let shift_width_assertion ~remove_trivial ~on_alarm (exp, typ) =
  let size = Cil.bitsSizeOf typ in
  shift_assertion ~remove_trivial ~on_alarm (exp, Some size)

(* The left operand of signed shifts should be nonnegative:
   implementation defined for right shift, undefined behavior for left shift. *)
let shift_negative_assertion ~remove_trivial ~on_alarm exp =
  shift_assertion ~remove_trivial ~on_alarm (exp, None)

(* Assertion for left and right shift overflow: the result should be
   representable in the result type.  *)
let shift_overflow_assertion ~signed ~remove_trivial ~on_alarm (exp, op, lexp, rexp) =
  let t = Cil.unrollType (Cil.typeOf exp) in
  let size = Cil.bitsSizeOf t in
  if size <> Cil.bitsSizeOf (Cil.typeOf lexp) then
    (* size of result type should be size of left (promoted) operand *)
    Options.warning ~current:true ~once:true
      "problem with bitsSize of %a: not treated" Printer.pp_exp exp;
  if op = Shiftlt then
    (* compute greatest representable "size bits" (signed) integer *)
    let maxValResult =
      if signed
      then Cil.max_signed_number size
      else Cil.max_unsigned_number size
    in
    let overflow_alarm ?(invalid=false) () =
      let signed = if signed then Alarms.Signed else Alarms.Unsigned in
      let a = Alarms.Overflow (signed, exp, maxValResult, Alarms.Upper_bound) in
      on_alarm ~invalid a;
    in
    if remove_trivial then begin
      match get_expr_val lexp, get_expr_val rexp with
      | None,_ | _, None ->
        overflow_alarm ()
      | Some lval64, Some rval64 ->
        (* both operands are constant: check result is representable in
           result type *)
        if Integer.ge rval64 Integer.zero
        && Integer.gt (Integer.shift_left lval64 rval64) maxValResult
        then
          overflow_alarm ~invalid:true ()
    end
    else overflow_alarm ()

(* Assertion for downcasts. *)
let downcast_assertion ~remove_trivial ~on_alarm (dst_type, exp) =
  let src_type = Cil.typeOf exp in
  let src_signed = Cil.isSignedInteger src_type in
  let dst_signed = Cil.isSignedInteger dst_type in
  let src_size = Cil.bitsSizeOf src_type in
  let dst_size = Cil.bitsSizeOfBitfield dst_type in
  if dst_size < src_size || dst_size == src_size && dst_signed <> src_signed
  then
    let dst_min, dst_max =
      if dst_signed
      then Cil.min_signed_number dst_size, Cil.max_signed_number dst_size
      else Integer.zero, Cil.max_unsigned_number dst_size
    in
    let overflow_kind =
      if Cil.isPointerType src_type
      then Alarms.Pointer_downcast
      else if dst_signed
      then Alarms.Signed_downcast
      else Alarms.Unsigned_downcast
    in
    let alarm ?(invalid=false) bound bound_kind =
      let a = Alarms.Overflow (overflow_kind, exp, bound, bound_kind) in
      on_alarm ~invalid a;
    in
    let alarms () =
      alarm dst_max Upper_bound;
      (* unsigned values cannot overflow in the negative *)
      if src_signed then alarm dst_min Lower_bound;
    in
    match remove_trivial, get_expr_val exp with
    | true, Some a64 ->
      let invalid = true in
      if Integer.lt a64 dst_min then alarm ~invalid dst_min  Lower_bound
      else if Integer.gt a64 dst_max then alarm ~invalid dst_max Upper_bound
    | _ -> alarms ()

(* assertion for casting a floating-point value to an integer *)
let float_to_int_assertion ~remove_trivial ~on_alarm (ty, exp) =
  let e_typ = Cil.unrollType (Cil.typeOf exp) in
  match e_typ, ty with
  | TFloat _, TInt (ikind,_) ->
    let szTo = Cil.bitsSizeOfBitfield ty in
    let min_ty, max_ty =
      if Cil.isSigned ikind then
        Cil.min_signed_number szTo, Cil.max_signed_number szTo
      else
        Integer.zero, Cil.max_unsigned_number szTo
    in
    let alarm ?(invalid=false) bk =
      let b = match bk with
        | Lower_bound -> min_ty
        | Upper_bound -> max_ty
      in
      on_alarm ~invalid (Alarms.Float_to_int (exp, b, bk))
    in
    let f = match exp.enode with
      | Const (CReal (f, _, _)) -> Some f
      | UnOp (Neg, { enode = Const (CReal (f, _, _))}, _) -> Some (-. f)
      | _ -> None
    in
    (match remove_trivial, f with
     | true, Some f ->
       begin
         try
           let fint = Floating_point.truncate_to_integer f in
           if Integer.lt fint min_ty then
             alarm ~invalid:true Lower_bound
           else if Integer.gt fint max_ty then
             alarm ~invalid:true Upper_bound
         with Floating_point.Float_Non_representable_as_Int64 sign ->
         match sign with
         | Floating_point.Neg -> alarm Lower_bound
         | Floating_point.Pos -> alarm Upper_bound
       end
     | _ ->
       alarm Upper_bound;
       alarm Lower_bound;
    )
  | _ -> ()

(* assertion for checking only finite float are used *)
let finite_float_assertion ~remove_trivial:_ ~on_alarm (fkind, exp) =
  let invalid = false in
  match Kernel.SpecialFloat.get () with
  | "none"       -> ()
  | "nan"        -> on_alarm ~invalid (Alarms.Is_nan (exp, fkind))
  | "non-finite" -> on_alarm ~invalid (Alarms.Is_nan_or_infinite (exp, fkind))
  | _            -> assert false

(* assertion for a pointer call [( *e )(args)]. *)
let pointer_call ~remove_trivial:_ ~on_alarm (e, args) =
  on_alarm ~invalid:false (Alarms.Function_pointer (e, Some args))

let rec is_safe_offset = function
  | NoOffset -> true
  | Field(fi,o) -> fi.fcomp.cstruct && not fi.faddrof && is_safe_offset o
  | Index(_,o) -> is_safe_offset o

let is_safe_pointer_value = function
  | Lval (Var vi, offset) ->
    (* Reading a pointer variable must emit an alarm if an invalid pointer value
       could have been written without previous alarm, through:
       - an union type, in which case [offset] is not NoOffset;
       - an untyped write, in which case the address of [vi] is taken. *)
    not vi.vaddrof && is_safe_offset offset
  | AddrOf (_, NoOffset) | StartOf (_, NoOffset) -> true
  | CastE (_typ, e) ->
    (* 0 can always be converted into a NULL pointer. *)
    let v = get_expr_val e in
    Option.fold ~none:false ~some:Integer.(equal zero) v
  | _ -> false

let pointer_value ~remove_trivial ~on_alarm expr =
  if not (remove_trivial && is_safe_pointer_value expr.enode)
  then on_alarm ~invalid:false (Alarms.Invalid_pointer expr)

let bool_value ~remove_trivial ~on_alarm lv =
  match remove_trivial, lv with
  | true, (Var vi, NoOffset)
    when (* consider as trivial accesses to ...  *)
      (not vi.vglob) && (* local variable or formal parameter when ... *)
      (not vi.vaddrof)  (* their address is not taken *)
    -> ()
  | _ -> on_alarm ~invalid:false (Alarms.Invalid_bool lv)

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
