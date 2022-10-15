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

(* Implements Figure 3 of J. Signoles' JFLA'15 paper "Rester statique pour
   devenir plus rapide, plus précis et plus mince".
   Also implements a support for real numbers. *)

module Error = Error.Make(struct let phase = Options.Dkey.interval end)

(* ********************************************************************* *)
(* Basic datatypes and operations *)
(* ********************************************************************* *)

type ival =
  | Ival of Ival.t
  | Float of fkind * float option (* a float constant, if any *)
  | Rational
  | Real
  | Nan

module D =
  Datatype.Make_with_collections
    (struct
      type t = ival
      let name = "E_ACSL.Interval.t"
      let reprs = [ Float (FFloat, Some 0.); Rational; Real; Nan ]
      include Datatype.Undefined

      let compare i1 i2 =
        if i1 == i2 then 0
        else
          match i1, i2 with
          | Ival i1, Ival i2 ->
            Ival.compare i1 i2
          | Float (k1, f1), Float (k2, f2) ->
            (* faster to compare a kind than a float *)
            let n = Stdlib.compare k1 k2 in
            if n = 0 then Stdlib.compare f1 f2 else n
          | Ival _, (Float _ | Rational | Real | Nan)
          | Float _, (Rational | Real | Nan)
          | Rational, (Real | Nan)
          | Real, Nan ->
            -1
          | Nan, (Ival _ | Float _ | Rational | Real)
          | Real, (Ival _ | Float _ | Rational)
          | Rational, (Ival _ | Float _)
          | Float _, Ival _ ->
            1
          | Rational, Rational | Real, Real | Nan, Nan ->
            assert false

      let equal = Datatype.from_compare

      let hash = function
        | Ival i -> 7 * Ival.hash i
        | Float(k, f) -> 17 * Hashtbl.hash f + 97 * Hashtbl.hash k
        | Rational -> 787
        | Real -> 1011
        | Nan -> 1277

      let pretty fmt = function
        | Ival i -> Ival.pretty fmt i
        | Float(_, Some f) -> Format.pp_print_float fmt f
        | Float(FFloat, None) -> Format.pp_print_string fmt "float"
        | Float(FDouble, None) -> Format.pp_print_string fmt "double"
        | Float(FLongDouble, None) -> Format.pp_print_string fmt "long double"
        | Rational -> Format.pp_print_string fmt "Rational"
        | Real -> Format.pp_print_string fmt "Real"
        | Nan -> Format.pp_print_string fmt "NaN"

    end)

let is_included i1 i2 = match i1, i2 with
  | Ival i1, Ival i2 -> Ival.is_included i1 i2
  | Float(k1, f1), Float(k2, f2) ->
    Stdlib.compare k1 k2 <= 0
    && (match f1, f2 with
        | None, None | Some _, None -> true
        | None, Some _ -> false
        | Some f1, Some f2 -> f1 = f2)
  | (Ival _ | Float _ | Rational), (Rational | Real)
  | Real, Real
  | Nan, Nan ->
    true
  (* floats and integer are not comparable: *)
  | Ival _, Float _ | Float _, Ival _
  (* nan is comparable to noone, but itself: *)
  | (Ival _ | Float _ | Rational | Real), Nan
  | Nan, (Ival _ | Float _ | Rational | Real)
  (* cases for reals and rationals: *)
  | Real, (Ival _ | Float _ | Rational)
  | Rational, (Ival _ | Float _) ->
    false

let widen = function
  | Ival iv ->
    let min, max = Ival.min_and_max iv in
    Ival (Ival.inject_range min max)
  | Float _ | Rational | Real | Nan as i -> i

let lift_unop f = function
  | Ival iv -> Ival (f iv)
  | Float _ ->
    (* any unary operator over a float generates a rational
       TODO: actually, certainly possible to generate a float *)
    Rational
  | Rational | Real | Nan as i ->
    i

let lift_arith_binop f i1 i2 = match i1, i2 with
  | Ival i1, Ival i2 ->
    Ival (f i1 i2)
  | (Ival _ | Float _), Float _
  | Float _, Ival _
  | (Ival _ | Float _ | Rational), Rational
  | Rational, (Ival _ | Float _) ->
    Rational
  | (Ival _ | Float _ | Rational | Real), Real
  | Real, (Ival _ | Float _ | Rational) ->
    Real
  | (Ival _ | Float _ | Rational | Real | Nan), Nan
  | Nan, (Ival _ | Float _ | Rational | Real) ->
    Nan

let join i1 i2 = match i1, i2 with
  | Ival iv, i when Ival.is_bottom iv -> i
  | i, Ival iv when Ival.is_bottom iv -> i
  | Ival i1, Ival i2 ->
    Ival (Ival.join i1 i2)
  | Float(k1, _), Float(k2, _) ->
    let k = if Cil.frank k1 >= Cil.frank k2 then k1 else k2 in
    Float(k, None (* lost value, if any before *))
  | Ival iv, Float(k, _)
  | Float(k, _), Ival iv ->
    begin
      match Ival.min_and_max iv with
      | None, None ->
        (* unbounded integers *)
        Rational
      | Some min, Some max ->
        (* if the interval of integers fits into the float types, then return
           this float type; otherwise return Rational *)
        (try
           let to_float n = Int64.to_float (Integer.to_int64_exn n) in
           let mini, maxi = to_float min, to_float max in
           let minf, maxf = match k with
             | FFloat ->
               Floating_point.most_negative_single_precision_float,
               Floating_point.max_single_precision_float
             | FDouble ->
               -. Float.max_float,
               Float.max_float
             | FLongDouble ->
               raise Exit
           in
           if mini >= minf && maxi <= maxf then Float(k, None) else Rational
         with Z.Overflow | Exit ->
           Rational)
      | None, Some _ | Some _, None ->
        assert false
    end
  | (Ival _ | Float _ | Rational), (Float _ | Rational)
  | Rational, Ival _ ->
    Rational
  | (Ival _ | Float _ | Rational | Real), Real
  | Real, (Ival _ | Float _ | Rational) ->
    Real
  | (Ival _ | Float _ | Rational | Real | Nan), Nan
  | Nan, (Ival _ | Float _ | Rational | Real) ->
    Nan

let meet i1 i2 = match i1, i2 with
  | Ival iv, _ when Ival.is_bottom iv -> Ival iv
  | _, Ival iv when Ival.is_bottom iv -> Ival iv
  | Ival i1, Ival i2 ->
    Ival (Ival.meet i1 i2)
  | Float(k1, Some f1), Float(k2, Some f2) ->
    if Float.equal f1 f2 then
      let k = if Cil.frank k1 >= Cil.frank k2 then k2 else k1 in
      Float (k, Some f1)
    else Ival Ival.bottom
  | Float(k, Some f), Float(k', None)
  | Float(k',None), Float(k, Some f) ->
    let f_in_k' = match k' with
      | FFloat ->
        let minf,maxf =
          Floating_point.most_negative_single_precision_float,
          Floating_point.max_single_precision_float
        in minf <= f && f <= maxf
      | FDouble
      | FLongDouble ->
        true
    in if f_in_k' then Float(k, Some f) else Ival Ival.bottom
  | Float(k1, None), Float(k2, None) ->
    let k = if Cil.frank k1 >= Cil.frank k2 then k2 else k1 in
    Float(k, None)
  | Float(k, Some f), Ival iv
  | Ival iv, Float(k, Some f) ->
    begin
      match Ival.min_and_max iv with
      | None, None ->
        (* unbounded integers *)
        Float(k, Some f)
      | Some min, Some max ->
        (* if the float type fits into the interval of integers, then return
           this float type; otherwise return Rational *)
        (try
           let to_float n = Int64.to_float (Integer.to_int64_exn n) in
           let mini, maxi = to_float min, to_float max in
           if mini <= f && maxi >= f then Float(k, Some f) else Ival Ival.bottom
         with Z.Overflow | Exit ->
           Rational)
      | None, Some _ | Some _, None ->
        assert false
    end
  | Ival iv, Float(k, None)
  | Float(k, None), Ival iv ->
    begin
      match Ival.min_and_max iv with
      | None, None ->
        (* unbounded integers *)
        Float(k, None)
      | Some min, Some max ->
        (* if the float type fits into the interval of integers, then return
           this float type; otherwise return Rational *)
        (try
           let to_float n = Int64.to_float (Integer.to_int64_exn n) in
           let mini, maxi = to_float min, to_float max in
           let minf, maxf = match k with
             | FFloat ->
               Floating_point.most_negative_single_precision_float,
               Floating_point.max_single_precision_float
             | FDouble ->
               -. Float.max_float,
               Float.max_float
             | FLongDouble ->
               raise Exit
           in
           if mini <= minf && maxi >= maxf then Float(k, None) else Rational
         with Z.Overflow | Exit ->
           Rational)
      | None, Some _ | Some _, None ->
        assert false
    end
  | (Ival _ | Float _ | Rational), (Float _ | Rational)
  | Rational, Ival _ ->
    Rational
  | (Ival _ | Float _ | Rational | Real), Real
  | Real, (Ival _ | Float _ | Rational) ->
    Real
  | (Ival _ | Float _ | Rational | Real | Nan), Nan
  | Nan, (Ival _ | Float _ | Rational | Real) ->
    Nan

let is_singleton_int = function
  | Ival iv -> Ival.is_singleton_int iv
  | Float _ | Rational | Real | Nan -> false

(* TODO: soundness of any downcast is not checked *)
let cast ~src ~dst = match src, dst with
  | Ival i1, Ival i2 ->
    Ival (Ival.meet i1 i2)
  | _, Float(_, Some _) ->
    assert false
  | Rational, Real
  | Float _, (Rational | Real) ->
    src
  | _, _ ->
    (* No need to optimize the other cases: if someone writes a cast
       (in particular, from integer to float/real or conversely), it is
       certainly on purpose . *)
    dst

(* a-b; or 0 if negative *)
let length a b = Z.max Z.zero (Z.add Z.one (Z.sub a b))

(* minimal distance between two intervals given by their respective lower and
   upper bounds, i.e. the length between the lower bound of the second interval
   bound and the upper bound of the first interval. *)
let min_delta (_, max1) (min2, _) = match max1, min2 with
  | Some m1, Some m2 -> length m2 m1
  | _, None | None, _ -> Z.zero

(* maximal distance between between two intervals given by their respective
   lower and upper bounds, i.e. the length between the upper bound of the second
   interval and the lower bound of the first interval.
   @return None for \infty *)
let max_delta (min1, _) (_, max2) = match min1, max2 with
  | Some m1, Some m2 -> Some (length m2 m1)
  | _, None | None, _ -> None

(* ********************************************************************* *)
(* constructors and destructors *)
(* ********************************************************************* *)

let extract_ival = function
  | Ival iv -> iv
  | Float _ | Rational | Real | Nan -> assert false

let bottom = Ival Ival.bottom
let top_ival = Ival (Ival.inject_range None None)
let singleton n = Ival (Ival.inject_singleton n)
let singleton_of_int n = singleton (Integer.of_int n)
let ival min max = Ival (Ival.inject_range (Some min) (Some max))

let interv_of_unknown_block =
  (* since we have no idea of the size of this block, we take the largest
     possible one which is unfortunately quite large *)
  lazy (ival Integer.zero (Bit_utils.max_byte_address ()))

(* ********************************************************************* *)
(* main algorithm *)
(* ********************************************************************* *)

(* The boolean indicates whether we have real numbers *)
let rec interv_of_typ ty = match Cil.unrollType ty with
  | TInt (k,_) as ty ->
    let n = Cil.bitsSizeOf ty in
    let l, u =
      if Cil.isSigned k then Cil.min_signed_number n, Cil.max_signed_number n
      else Integer.zero, Cil.max_unsigned_number n
    in
    ival l u
  | TEnum(enuminfo, _) ->
    interv_of_typ (TInt(enuminfo.ekind, []))
  | _ when Gmp_types.Z.is_t ty ->
    top_ival
  | TFloat (k, _) ->
    Float(k, None)
  | _ when Gmp_types.Q.is_t ty ->
    Rational (* only rationals are implemented *)
  | TVoid _ | TPtr _ | TArray _ | TFun _ | TComp _ | TBuiltin_va_list _ ->
    Nan
  | TNamed _ ->
    assert false

let extended_interv_of_typ ty = match interv_of_typ ty with
  | Ival iv ->
    let l,u = Ival.min_int iv, Ival.max_int iv in
    let u = match u with
      | Some u -> Some (Integer.add u Integer.one)
      | None -> None
    in
    Ival (Ival.inject_range l u);
  | Rational | Real | Nan | Float (_,_) as i
    -> i

let interv_of_logic_typ = function
  | Ctype ty -> interv_of_typ ty
  | Linteger -> top_ival
  | Lreal -> Real
  | Ltype _ -> Error.not_yet "user-defined logic type"
  | Lvar _ -> Error.not_yet "type variable"
  | Larrow _ -> Nan

let ikind_of_ival iv =
  if Ival.is_bottom iv then IInt
  else match Ival.min_and_max iv with
    | Some l, Some u ->
      let is_pos = Integer.ge l Integer.zero in
      let lkind = Cil.intKindForValue l is_pos in
      let ukind = Cil.intKindForValue u is_pos in
      (* kind corresponding to the interval *)
      let kind = if Cil.intTypeIncluded lkind ukind then ukind else lkind in
      (* convert the kind to [IInt] whenever smaller. *)
      if Cil.intTypeIncluded kind IInt then IInt else kind
    | None, None -> raise Cil.Not_representable (* GMP *)
    (* TODO: do not raise an exception, but returns a value instead *)
    | None, Some _ | Some _, None ->
      (* Semi-open interval that can happen when computing the interval of shift
         operations if the computation overflows *)
      (* TODO: do not raise an exception, but returns a value instead *)
      raise Cil.Not_representable (* GMP *)

(* function call profiles (intervals for their formal parameters) *)
module Profile = struct
  include Datatype.List_with_collections
      (D)
      (struct
        let module_name = "E_ACSL.Interval.Logic_function_env.Profile"
      end)
  let is_included p1 p2 = List.for_all2 is_included p1 p2
end

(* Imperative environments *)
module rec Env: sig
  val clear: unit -> unit
  val add: Cil_types.logic_var -> ival -> unit
  val find: Cil_types.logic_var -> ival
  val remove: Cil_types.logic_var -> unit
end = struct

  open Cil_datatype
  let tbl: ival Logic_var.Hashtbl.t = Logic_var.Hashtbl.create 7

  (* TODO: when adding, also join with the old value (if any). Would certainly
     be the correct way to handle a \let in a recursive logic functions (if the
     \let body depends on one formal) *)
  let add = Logic_var.Hashtbl.add tbl
  let remove = Logic_var.Hashtbl.remove tbl
  let find = Logic_var.Hashtbl.find tbl

  let clear () =
    Logic_var.Hashtbl.clear tbl;
    Logic_function_env.clear ()

end

(* Environment for handling logic functions *)
and Logic_function_env: sig
  val widen: infer:(term -> ival) -> term -> ival -> bool * ival
  val clear: unit -> unit
end = struct

  (* The environment associates to each term (denoting a logic function
     application) a profile, i.e. the list of intervals for its formal
     parameters.  It helps to type these applications.

     For each pair of function name and profile, an interval containing the
     result is also stored. It helps to generate the function definitions for
     each logic function (for each function, one definition per profile) . *)

  module Terms = Hashtbl.Make
      (struct
        type t = term
        let equal = (==)
        let hash = Cil_datatype.Term.hash
      end)

  module LF =
    Datatype.Pair_with_collections
      (Datatype.String)
      (Profile)
      (struct
        let module_name = "E_ACSL.Interval.Logic_function_env.LF"
      end)

  let terms: Profile.t Terms.t = Terms.create 7
  let named_profiles = LF.Hashtbl.create 7

  let clear () =
    Terms.clear terms;
    LF.Hashtbl.clear named_profiles

  let interv_of_typ_containing_interv = function
    | Float _ | Rational | Real | Nan as x ->
      x
    | Ival i ->
      try
        let kind = ikind_of_ival i in
        interv_of_typ (TInt(kind, []))
      with Cil.Not_representable ->
        top_ival

  let rec map3 f l1 l2 l3 = match l1, l2, l3 with
    | [], [], [] -> []
    | x1 :: l1, x2 :: l2, x3 :: l3 -> f x1 x2 x3 :: map3 f l1 l2 l3
    | _, _, _ -> invalid_arg "E_ACSL.Interval.map3"

  let extract_profile ~infer old_profile t = match t.term_node with
    | Tapp(li, _, args) ->
      let old_profile = match old_profile with
        | None -> List.map (fun _ -> bottom) li.l_profile
        | Some p -> p
      in
      li.l_var_info.lv_name,
      map3
        (fun param old_i arg ->
           let i = infer arg in
           (* over-approximation of the interval to reach the fixpoint
              faster, and to generate fewer specialized functions *)
           let larger_i = interv_of_typ_containing_interv i in
           (* merge the old profile and the new one *)
           let new_i = join larger_i old_i in
           Env.add param new_i;
           new_i)
        li.l_profile
        old_profile
        args
    | _ ->
      assert false

  let widen_one_callsite ~infer old_profile t i =
    let (_, p as named_p) = extract_profile ~infer old_profile t in
    try
      let old_i = LF.Hashtbl.find named_profiles named_p in
      if is_included i old_i then true, p, old_i (* fixpoint reached *)
      else begin
        let j = join i old_i in
        LF.Hashtbl.replace named_profiles named_p j;
        false, p, j
      end
    with Not_found ->
      LF.Hashtbl.add named_profiles named_p i;
      false, p, i

  let widen ~infer t i =
    try
      let old_p = Terms.find terms t in
      let is_included, new_p, i = widen_one_callsite ~infer (Some old_p) t i in
      if Profile.is_included new_p old_p then is_included, i
      else begin
        Terms.replace terms t new_p;
        false, i
      end
    with Not_found ->
      let is_included, p, i = widen_one_callsite ~infer None t i in
      Terms.add terms t p;
      is_included, i

end

(* ********************************************************************* *)
(* Main functions *)
(* ********************************************************************* *)

let infer_sizeof ty =
  try singleton_of_int (Cil.bytesSizeOf ty)
  with Cil.SizeOfError _ -> interv_of_typ Cil.theMachine.Cil.typeOfSizeOf

let infer_alignof ty =
  try singleton_of_int (Cil.bytesAlignOf ty)
  with Cil.SizeOfError _ -> interv_of_typ Cil.theMachine.Cil.typeOfSizeOf

(* Infer the interval of an extended quantifier \sum or \product.
   [lambda] is the interval of the lambda term, [min] (resp. [max]) is the
   interval of the minimum (resp. maximum) and [oper] is the identifier of the
   extended quantifier (\sum, or \product). The returned ival is the interval of
   the extended quantifier. *)
let infer_sum_product oper lambda min max = match lambda, min, max with
  | Ival lbd_iv, Ival lb_iv, Ival ub_iv ->
    (try
       let min_lambda, max_lambda = Ival.min_and_max lbd_iv in
       let minmax_lb = Ival.min_and_max lb_iv in
       let minmax_ub = Ival.min_and_max ub_iv in
       let lb, ub = match oper.lv_name with
         | "\\sum" ->
           (* the lower (resp. upper) bound is the min (resp. max) value of the
              lambda term, times the min (resp. max) distance between them if
              the sign is positive, or conversely if the sign is negative *)
           let lb = match min_lambda with
             | None -> None
             | Some z ->
               if Z.sign z = -1
               then Option.map (Z.mul z) (max_delta minmax_lb minmax_ub)
               else Some (Z.mul z (min_delta minmax_lb minmax_ub))
           in
           let ub = match max_lambda with
             | None -> None
             | Some z ->
               if Z.sign z = -1
               then Some (Z.mul z (min_delta minmax_lb minmax_ub))
               else Option.map (Z.mul z) (max_delta minmax_lb minmax_ub)
           in
           lb, ub
         | "\\product" ->
           (* the lower (resp. upper) bound is the min (resp. max) value of the
              lambda term in absolute value, power the min (resp. max) distance
              between them if the sign is positive, or conversely for both the
              lambda term and the exponent if the sign is negative. If the sign
              is negative, the minimum is also negative. *)
           let min, max =
             match min_lambda, max_lambda with
             | None, None as res -> res
             | None, Some m | Some m, None -> Some m, None
             | Some min, Some max ->
               let abs_min = Z.abs min in
               let abs_max = Z.abs max in
               Some (Z.min abs_min abs_max), Some (Z.max abs_min abs_max)
           in
           let lb = match min_lambda with
             | None -> None
             | Some z ->
               if Z.sign z = -1 then
                 (* the lower bound is (possibly) negative *)
                 Extlib.opt_map2
                   (fun m max ->
                      match min_lambda, max_lambda with
                      | Some mil, Some mal when Z.lt (Z.abs mil) (Z.abs mal) ->
                        (* [lambda] contains both positive and negative values
                           and |mil| < |mal|: instead of [-mal^m], the min is
                           optimized to [mil * mal^(m-1)] *)
                        Z.mul mil (Z.pow max (Z.to_int m - 1))
                      | None, _ | _, None | Some _, Some _ ->
                        Z.neg (Z.pow max (Z.to_int m)))
                   (max_delta minmax_lb minmax_ub)
                   max
               else
                 (* all numbers are positive:
                    the lower bound is necessarily positive *)
                 Option.map
                   (fun m -> Z.pow m (Z.to_int (min_delta minmax_lb minmax_ub)))
                   min
           in
           let ub =
             Extlib.opt_map2
               (fun m max ->
                  match max_lambda with
                  | Some ml when Z.lt ml Z.zero && not (Z.equal m Z.one) ->
                    (* when [lambda] is necessarily negative with an odd number
                       of iterations (>1), the result is necessarily negative,
                       so smaller than the maximal (positive) value. Therefore,
                       it is possible to reduce the number of iteration by 1. *)
                    let exp = Z.to_int m in
                    Z.pow max (exp - exp mod 2)
                  | None | Some _ ->
                    Z.pow max (Z.to_int m))
               (max_delta minmax_lb minmax_ub)
               max
           in
           lb, ub
         | s ->
           Options.fatal "unexpect logic function '%s'" s
       in
       Ival (Ival.inject_range lb ub)
     with
     | Abstract_interp.Error_Bottom -> bottom
     | Z.Overflow (* if the exponent of \product is too high *) -> top_ival)
  | _ -> Error.not_yet "extended quantifiers with non-integer parameters"

let rec infer t =
  let get_cty t = match t.term_type with Ctype ty -> ty | _ -> assert false in
  match t.term_node with
  | TConst (Integer (n, _)) -> singleton n
  | TConst (LChr c) ->
    let n = Cil.charConstToInt c in
    singleton n
  | TConst (LEnum enumitem) ->
    let rec find_idx n = function
      | [] -> assert false
      | ei :: l -> if ei == enumitem then n else find_idx (n + 1) l
    in
    let n = Integer.of_int (find_idx 0 enumitem.eihost.eitems) in
    singleton n
  | TLval lv -> infer_term_lval lv
  | TSizeOf ty -> infer_sizeof ty
  | TSizeOfE t -> infer_sizeof (get_cty t)
  | TSizeOfStr str -> singleton_of_int (String.length str + 1 (* '\0' *))
  | TAlignOf ty -> infer_alignof ty
  | TAlignOfE t -> infer_alignof (get_cty t)

  | TUnOp (Neg, t) ->
    let i = infer t in
    lift_unop Ival.neg_int i
  | TUnOp (BNot, t) ->
    let i = infer t in
    lift_unop Ival.bitwise_signed_not i
  | TUnOp (LNot, _)
  | TBinOp ((Lt | Gt | Le | Ge | Eq | Ne | LAnd | LOr), _, _) ->
    Ival Ival.zero_or_one

  | TBinOp (PlusA, t1, t2) ->
    let i1 = infer t1 in
    let i2 = infer t2 in
    lift_arith_binop Ival.add_int i1 i2
  | TBinOp (MinusA, t1, t2) ->
    let i1 = infer t1 in
    let i2 = infer t2 in
    lift_arith_binop Ival.sub_int i1 i2
  | TBinOp (Mult, t1, t2) ->
    let i1 = infer t1 in
    let i2 = infer t2 in
    lift_arith_binop Ival.mul i1 i2
  | TBinOp (Div, t1, t2) ->
    let i1 = infer t1 in
    let i2 = infer t2 in
    lift_arith_binop Ival.div i1 i2
  | TBinOp (Mod, t1, t2) ->
    let i1 = infer t1 in
    let i2 = infer t2 in
    lift_arith_binop Ival.c_rem i1 i2
  | TBinOp (Shiftlt, t1, t2) ->
    let i1 = infer t1 in
    let i2 = infer t2 in
    lift_arith_binop Ival.shift_left i1 i2
  | TBinOp (Shiftrt, t1, t2) ->
    let i1 = infer t1 in
    let i2 = infer t2 in
    lift_arith_binop Ival.shift_right i1 i2
  | TBinOp (BAnd, t1, t2) ->
    let i1 = infer t1 in
    let i2 = infer t2 in
    lift_arith_binop Ival.bitwise_and i1 i2
  | TBinOp (BXor, t1, t2) ->
    let i1 = infer t1 in
    let i2 = infer t2 in
    lift_arith_binop Ival.bitwise_xor i1 i2
  | TBinOp (BOr, t1, t2) ->
    let i1 = infer t1 in
    let i2 = infer t2 in
    lift_arith_binop Ival.bitwise_or i1 i2
  | TCastE (ty, t) ->
    let src = infer t in
    let dst = interv_of_typ ty in
    cast ~src ~dst
  | Tif (_, t2, t3) ->
    let i2 = infer t2 in
    let i3 = infer t3 in
    join i2 i3
  | Tat (t, _) ->
    infer t
  | TBinOp (MinusPP, t, _) ->
    (match Cil.unrollType (get_cty t) with
     | TArray(_, _, _) as ta ->
       begin
         try
           let n = Cil.bitsSizeOf ta in
           (* the second argument must be in the same block than [t].
              Consequently the result of the difference belongs to
              [0; \block_length(t)] *)
           let nb_bytes = if n mod 8 = 0 then n / 8 else n / 8 + 1 in
           ival Integer.zero (Integer.of_int nb_bytes)
         with Cil.SizeOfError _ ->
           Lazy.force interv_of_unknown_block
       end
     | TPtr _ ->
       Lazy.force interv_of_unknown_block
     | _ -> assert false)
  | Tblock_length (_, t)
  | Toffset(_, t) ->
    (match Cil.unrollType (get_cty t) with
     | TArray(_, _, _) as ta ->
       begin
         try
           let n = Cil.bitsSizeOf ta in
           let nb_bytes = if n mod 8 = 0 then n / 8 else n / 8 + 1 in
           singleton_of_int nb_bytes
         with Cil.SizeOfError _ ->
           Lazy.force interv_of_unknown_block
       end
     | TPtr _ -> Lazy.force interv_of_unknown_block
     | _ -> assert false)
  | Tnull  -> singleton_of_int 0
  | TLogic_coerce (_, t) -> infer t
  | Tapp (li, lst, args) ->
    (match li.l_body with
     | LBpred _ ->
       Ival Ival.zero_or_one
     | LBterm t' ->
       let rec fixpoint i =
         let is_included, new_i =
           Logic_function_env.widen ~infer t i
         in
         if is_included then begin
           List.iter (fun lv -> Env.remove lv) li.l_profile;
           new_i
         end else
           let i = infer t' in
           List.iter (fun lv -> Env.remove lv) li.l_profile;
           fixpoint i
       in
       fixpoint bottom
     | LBnone when li.l_var_info.lv_name = "\\sum" ||
                   li.l_var_info.lv_name = "\\product" ->
       (match args with
        | [ t1; t2; { term_node = Tlambda([ k ], _) } as lambda ] ->
          let t1_iv = infer t1 in
          let t2_iv = infer t2 in
          let k_iv = join t1_iv t2_iv in
          Env.add k k_iv;
          let lambda_iv = infer lambda in
          Env.remove k;
          let t2incr =
            Logic_const.term (TBinOp(PlusA, t2, Cil.lone ())) Linteger
          in
          (* it is correct and precise to use k_ival to compute lambda_ival, but
             not during the code generation since the type used for k is the
             greatest type between the type of t1 and the type of t2+1, that is
             why the ival associated to k is updated *)
          Env.add k (join t1_iv (infer t2incr));
          (* k is removed during code generation, it is needed for generating
             the code of the lambda term *)
          infer_sum_product li.l_var_info lambda_iv t1_iv t2_iv
        | _ -> Error.not_yet "extended quantifiers without lambda term")
     | LBnone when li.l_var_info.lv_name = "\\numof" ->
       (match args with
        | [ t1; t2; { term_node = Tlambda([ k ], p) } ] ->
          let logic_info = Cil_const.make_logic_info "\\sum" in
          logic_info.l_type <- li.l_type;
          logic_info.l_tparams <- li.l_tparams;
          logic_info.l_labels <- li.l_labels;
          logic_info.l_profile <- li.l_profile;
          logic_info.l_body <- li.l_body;
          let numof_as_sum =
            let conditional_term =
              Logic_const.term
                (Tif(p, Cil.lone (), Cil.lzero ())) Linteger
            in
            let lambda_term =
              Logic_const.term (Tlambda([ k ], conditional_term)) Linteger
            in
            (Logic_const.term
               (Tapp(logic_info, lst, [ t1; t2; lambda_term ])) Linteger)
          in infer numof_as_sum
        | _ ->
          Options.fatal "unexpected input for an extended quantifier \\numof")
     | LBnone
     | LBreads _ ->
       (match li.l_type with
        | None -> assert false
        | Some ret_type -> interv_of_logic_typ ret_type)
     | LBinductive _ ->
       Error.not_yet "logic functions inductively defined")

  | Tunion _ -> Error.not_yet "tset union"
  | Tinter _ -> Error.not_yet "tset intersection"
  | Tcomprehension (_,_,_) -> Error.not_yet "tset comprehension"
  | Trange(Some n1, Some n2) ->
    let i1 = infer n1 in
    let i2 = infer n2 in
    join i1 i2
  | Trange(None, _) | Trange(_, None) ->
    Options.abort "unbounded ranges are not part of E-ACSl"

  | Tlet (li, t) ->
    let li_t = Misc.term_of_li li in
    let li_v = li.l_var_info in
    let i1 = infer li_t in
    Env.add li_v i1;
    let i2 = infer t in
    Env.remove li_v;
    i2
  | TConst (LReal lr) ->
    if lr.r_lower = lr.r_upper then Float(FDouble, Some lr.r_nearest)
    else Rational
  | Tlambda ([ _ ],lt) ->
    infer lt
  | Tlambda (_,_)
  | TConst (LStr _ | LWStr _)
  | TBinOp (PlusPI,_,_)
  | TBinOp (MinusPI,_,_)
  | TAddrOf _
  | TStartOf _
  | TDataCons (_,_)
  | Tbase_addr (_,_)
  | TUpdate (_,_,_)
  | Ttypeof _
  | Ttype _
  | Tempty_set ->
    Nan

and infer_term_lval (host, offset as tlv) =
  match offset with
  | TNoOffset -> infer_term_host host
  | _ ->
    let ty = Logic_utils.logicCType (Cil.typeOfTermLval tlv) in
    interv_of_typ ty

and infer_term_host thost =
  match thost with
  | TVar v ->
    (try Env.find v with Not_found ->
     match v.lv_type with
     | Linteger -> top_ival
     | Ctype (TFloat(fk, _)) -> Float(fk, None)
     | Lreal -> Real
     | Ctype _ -> interv_of_typ (Logic_utils.logicCType v.lv_type)
     | Ltype _ | Lvar _ | Larrow _ -> Options.fatal "unexpected logic type")
  | TResult ty ->
    interv_of_typ ty
  | TMem t ->
    let ty = Logic_utils.logicCType t.term_type in
    match Cil.unrollType ty with
    | TPtr(ty, _) | TArray(ty, _, _) ->
      interv_of_typ ty
    | _ ->
      Options.fatal "unexpected type %a for term %a"
        Printer.pp_typ ty
        Printer.pp_term t

let infer t =
  let i = infer t in
  Logic_function_env.clear();
  i

include D

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
 *)
