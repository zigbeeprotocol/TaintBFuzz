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

open Cvalue
open Cil_types
open Abstract_value
open Lattice_bounds

(* --------------------------------------------------------------------------
                               Comparison
   -------------------------------------------------------------------------- *)

(* Representation of a pointer value to a literal string, with the string
   itself, its length and the offsets pointed to in the string. *)
type str = { string: string; offset: Ival.t; length: int; }

(* Returns true if one string is a suffix of the other, and if there are offsets
   pointing to the same point in this suffix. *)
let may_be_suffix s1 s2 =
  (* Requires [s1.length] <= [s2.length]. *)
  let is_suffix s1 s2 =
    let sub2 = String.sub s2.string (s2.length - s1.length) s1.length in
    String.equal s1.string sub2 &&
    let delta = Integer.of_int (s1.length - s2.length) in
    let off2 = Ival.add_singleton_int delta s2.offset in
    not (Ival.is_bottom (Ival.narrow s1.offset off2))
  in
  if s1.length <= s2.length then is_suffix s1 s2 else is_suffix s2 s1

(* Returns true if [s1] may be shared with [s2] or a substring of [s2]. *)
let rec may_be_shared_within s1 s2 =
  may_be_suffix s1 s2 ||
  match String.rindex_opt s2.string '\x00' with
  | None -> false
  | Some i ->
    let s2 = { s2 with string = String.sub s2.string 0 i; length = i } in
    may_be_shared_within s1 s2

(* Returns true if [s1] and [s2] might point to the same literal string. *)
let may_be_shared str1 off1 str2 off2 =
  let s1 = { string = str1; offset = off1; length = String.length str1 }
  and s2 = { string = str2; offset = off2; length = String.length str2 } in
  may_be_shared_within s1 s2 || may_be_shared_within s2 s1

(* Checks if all string bases of [v] satisfy [f]. *)
let for_all_string v f =
  Locations.Location_Bytes.for_all
    (fun base off -> match base with
       | Base.String (_, Base.CSString str) -> f base str off
       | Base.String (_, Base.CSWstring _ ) -> false (* Not implemented yet *)
       | _ -> true)
    v

(* Literal strings can only be compared if their contents are recognizably
   different (or the strings are physically the same). *)
let are_comparable_string v1 v2 =
  for_all_string v1 (fun base1 str1 off1 ->
      for_all_string v2 (fun base2 str2 off2 ->
          Base.equal base1 base2 ||
          not (may_be_shared str1 off1 str2 off2)))

(* Under-approximation of the fact that a pointer is actually correct w.r.t.
   what can be created through pointer arithmetics. See C99 6.5.6 and 6.5.8
   for the definition of possible pointers, and in particular the definition
   of "one past". Value does not currently check that all pointers are
   possible, but flags impossible ones using pointer_comparable alarms when
   performing a comparison.

   In practice, function pointers are considered possible or one past
   when their offset is 0. For object pointers, the offset is checked
   against the validity of each base, taking past-one into account. *)
let possible_pointer access location =
  let location = Locations.loc_bytes_to_loc_bits location in
  let is_possible_offset base offs =
    if Base.is_function base
    then Ival.is_zero offs
    else Base.is_valid_offset access base offs
  in
  Locations.Location_Bits.for_all is_possible_offset location

(* Are [ev1] and [ev2] safely comparable, or does their comparison involves
   invalid pointers, or is undefined (typically pointers in different bases). *)
let are_comparable_reason kind ev1 ev2 =
  let open Locations in
  (* If both of the operands have arithmetic type, the comparison is valid. *)
  if Location_Bytes.is_included ev1 Location_Bytes.top_int
  && Location_Bytes.is_included ev2 Location_Bytes.top_int
  then true, `Ok
  else
    let null_1, rest_1 = Location_Bytes.split Base.null ev1
    and null_2, rest_2 = Location_Bytes.split Base.null ev2 in
    (* Note that here, rest_1 and rest_2 cannot be both bottom. *)
    let is_bottom1 = Location_Bytes.is_bottom rest_1
    and is_bottom2 = Location_Bytes.is_bottom rest_2 in
    let arith_compare_ok, reason =
      if kind = Abstract_value.Equality
      then
        (* A pointer can be compared to a null pointer constant
           by equality operators. *)
        if (Ival.is_included null_1 Ival.zero || is_bottom2)
        && (Ival.is_included null_2 Ival.zero || is_bottom1)
        then true, `Ok
        else false, `Eq_Different_bases_including_null
      else
        (* Pointers cannot be compared to arithmetic values by
           relational operators. *)
      if Ival.is_bottom null_1 && Ival.is_bottom null_2
      then true, `Ok
      else false, `Rel_Different_bases_including_null
    in
    if not arith_compare_ok
    then false, reason
    else
      (* Both pointers have to be almost valid (they can be pointers to one past
         an array object. *)
    if (not (possible_pointer Base.No_access rest_1)) ||
       (not (possible_pointer Base.No_access rest_2))
    then false, `Invalid_pointer
    else
      (* Equality operators allow the comparison between an almost valid pointer
         and the null pointer (other cases where is_bottom1 or is_bottom2 have
         been managed by arith_compare_ok). *)
    if is_bottom1 || is_bottom2
    then true, `Ok
    else
      (* If both pointers point to the same base, the comparison is valid. *)
      let single_base_ok =
        try
          let base_1, _ = Location_Bytes.find_lonely_key rest_1
          and base_2, _ = Location_Bytes.find_lonely_key rest_2 in
          Base.equal base_1 base_2
        with Not_found -> false
      in
      if single_base_ok
      then true, `Ok
      else if not (kind = Abstract_value.Equality)
      (* For relational operators, the comparison of pointers on different
         bases is undefined. *)
      then false, `Rel_different_bases
      else
        (* If both addresses are valid, they can be compared for equality. *)
      if (possible_pointer (Base.Read Integer.one) rest_1) &&
         (possible_pointer (Base.Read Integer.one) rest_2)
      then
        (* But beware of the comparisons of literal strings. *)
        if are_comparable_string rest_1 rest_2
        then true, `Ok
        else false, `Shareable_strings
      else false, `Invalid_pointer

let pp_incomparable_reason fmt = function
  | `Ok -> ()
  | `Shareable_strings ->
    Format.pp_print_string fmt
      "equality between pointers to strings that may overlap"
  | `Invalid_pointer ->
    Format.pp_print_string fmt "invalid pointer(s)"
  | `Rel_different_bases ->
    Format.pp_print_string fmt
      "relational comparison to pointers in different bases"
  | `Eq_Different_bases_including_null ->
    Format.pp_print_string fmt
      "equality between a pointer and a constant"
  | `Rel_Different_bases_including_null ->
    Format.pp_print_string fmt
      "relational comparison between a pointer and a constant"

let assume_comparable comparison v1 v2 =
  let ok = match comparison with
    | Abstract_value.Equality
    | Abstract_value.Relation ->
      let truth, reason = are_comparable_reason comparison v1 v2 in
      if reason <> `Ok then
        Self.result
          ~current:true ~once:true
          ~dkey:Self.dkey_pointer_comparison
          "invalid pointer comparison: %a" pp_incomparable_reason reason;
      truth
    | Abstract_value.Subtraction ->
      (* TODO: we may be able to reduce the bases that appear only on one side *)
      try
        let b1, _ = Cvalue.V.find_lonely_key v1
        and b2, _ = Cvalue.V.find_lonely_key v2 in
        Base.equal b1 b2
      with Not_found -> false
  in
  if ok
  then `True
  else `Unknown (v1, v2)

let are_comparable op ev1 ev2 =
  let kind = match op with
    | Abstract_interp.Comp.Eq
    | Abstract_interp.Comp.Ne -> Abstract_value.Equality
    | _ -> Abstract_value.Relation
  in
  fst (are_comparable_reason kind ev1 ev2)

(* --------------------------------------------------------------------------
                                    Alarms
   -------------------------------------------------------------------------- *)

let assume_non_zero value =
  if Cvalue.V.contains_zero value
  then
    if Cvalue.V.is_zero value
    then `False
    else
      let value = Cvalue.V.(diff value singleton_zero) in
      `Unknown value
  else `True

let assume_not_nan ~assume_finite fkind v =
  let kind = Fval.kind fkind in
  let evaluate, backward_propagate =
    if assume_finite
    then Fval.is_finite, Fval.backward_is_finite ~positive:true
    else Fval.is_not_nan, fun _fkind -> Fval.backward_is_nan ~positive:false
  in
  match Cvalue.V.project_float v with
  | exception Cvalue.V.Not_based_on_null ->
    if Cvalue.V.is_bottom v then `True else `Unknown v
  | res ->
    match evaluate res with
    | Abstract_interp.Comp.False -> `False
    | Abstract_interp.Comp.True -> `True
    | Abstract_interp.Comp.Unknown ->
      let res = Bottom.non_bottom (backward_propagate kind res) in
      `Unknown (V.inject_float res)

let nearly_valid_bits = function
  | Base.Empty
  | Base.Invalid -> Integer.zero, Integer.zero
  | Base.Known (min, max) | Base.Unknown (min, _, max) -> min, Integer.succ max
  | Base.Variable variable -> Integer.zero, Integer.succ variable.Base.max_alloc

let nearly_valid_offset base =
  let min, max = nearly_valid_bits base in
  let to_byte bound = Some (Integer.e_div bound (Bit_utils.sizeofchar ())) in
  Ival.inject_range (to_byte min) (to_byte max)

let assume_pointer loc =
  let aux base ival (acc_v, acc_ok) =
    let validity = Base.validity base in
    let nearly_valid_ival = nearly_valid_offset validity in
    let new_ival = Ival.narrow ival nearly_valid_ival in
    let ival, ok =
      if Base.is_null base && Ival.contains_zero ival
      then Ival.(join zero new_ival), acc_ok && Ival.is_zero ival
      else new_ival, acc_ok && Ival.equal ival new_ival
    in
    Locations.Location_Bytes.add base ival acc_v, ok
  in
  try
    let loc, ok = Cvalue.V.(fold_topset_ok aux loc (bottom, true)) in
    if Cvalue.V.is_bottom loc then `False
    else if ok then `True else `Unknown loc
  with Abstract_interp.Error_Top -> `Unknown loc

(* --------------------------------------------------------------------------
                              Integer overflow
   -------------------------------------------------------------------------- *)

let assume_bounded_fval bound_kind fval_bound fval =
  let open Abstract_interp.Comp in
  match bound_kind with
  | Lower_bound -> Fval.forward_comp Ge fval fval_bound
  | Upper_bound -> Fval.forward_comp Le fval fval_bound

let assume_bounded_float fkind bound_kind bound value =
  let open Abstract_interp.Comp in
  try
    let fval = V.project_float value in
    let fval_bound = Fval.inject_singleton (Fval.F.of_float bound) in
    match assume_bounded_fval bound_kind fval_bound fval with
    | False -> `False
    | True -> `True
    | Unknown ->
      let kind = Fval.kind fkind in
      let fval = match bound_kind with
        | Lower_bound -> Fval.backward_comp_left_true Ge kind fval fval_bound
        | Upper_bound -> Fval.backward_comp_left_true Le kind fval fval_bound
      in
      let fval = Bottom.non_bottom fval in
      `Unknown (Cvalue.V.inject_float fval)
  with V.Not_based_on_null -> `Unknown value

let assume_bounded_ival bound_kind bound ival =
  let open Abstract_interp.Comp in
  match bound_kind with
  | Lower_bound -> Ival.forward_comp_int Ge ival (Ival.inject_singleton bound)
  | Upper_bound -> Ival.forward_comp_int Le ival (Ival.inject_singleton bound)

(* Only reduces the integer part of the cvalue; pointer values are left
   unchanged. *)
let assume_bounded_int bound_kind bound value =
  let open Abstract_interp.Comp in
  let ival, pointer = V.split Base.null value in
  let status =
    if V.is_bottom pointer
    then assume_bounded_ival bound_kind bound ival
    else Unknown
  in
  match status with
  | False -> `False
  | True -> `True
  | Unknown ->
    let range = match bound_kind with
      | Lower_bound -> Ival.inject_range (Some bound) None
      | Upper_bound -> Ival.inject_range None (Some bound)
    in
    let ival = Ival.narrow ival range in
    let value = V.add Base.null ival value in
    assert (not (V.is_bottom value));
    `Unknown value

let assume_bounded bound_kind bound value =
  match bound with
  | Float (fbound, fkind) -> assume_bounded_float fkind bound_kind fbound value
  | Int ibound -> assume_bounded_int bound_kind ibound value

type integer_range = Eval_typ.integer_range = { i_bits: int; i_signed: bool }

let rewrap_integer range value =
  let size = Integer.of_int range.i_bits in
  V.cast_int_to_int ~signed:range.i_signed ~size value


(* --------------------------------------------------------------------------
                       Binary Operators Evaluation
   -------------------------------------------------------------------------- *)

let forward_minus_pp ~typ ev1 ev2 =
  let conv minus_offs =
    try
      let size = Int_Base.project (Bit_utils.osizeof_pointed typ) in
      if Integer.is_one size
      then minus_offs
      else Ival.scale_div ~pos:true size minus_offs
    with Abstract_interp.Error_Top -> Ival.top
  in
  if not (Parameters.WarnPointerSubstraction.get ()) then
    (* Generate garbled mix if the two pointers disagree on their base *)
    let minus_val = V.add_untyped ~factor:Int_Base.minus_one ev1 ev2 in
    try
      V.inject_ival (conv (Cvalue.V.project_ival minus_val))
    with Cvalue.V.Not_based_on_null ->
      V.join (V.topify_arith_origin ev1) (V.topify_arith_origin ev2)
  else
    (* Pointwise arithmetics.*)
    let v = V.sub_pointer ev1 ev2 in
    try V.inject_ival (conv (Cvalue.V.project_ival v))
    (* [sub_pointer] returns an ival or a garbled mix. In the later case,
       no need to topify the result. *)
    with Cvalue.V.Not_based_on_null -> v

(* Evaluation of some operations on Cvalue.V. [typ] is the type of [ev1].
   The function must behave as if it was acting on unbounded integers *)
let forward_binop_int ~typ ev1 op ev2 =
  match op with
  | PlusPI  -> V.add_untyped ~factor:(Bit_utils.osizeof_pointed typ) ev1 ev2
  | MinusPI ->
    let int_base = Int_Base.neg (Bit_utils.osizeof_pointed typ) in
    V.add_untyped ~factor:int_base ev1 ev2
  | PlusA   -> V.add_untyped ~factor:(Int_Base.one) ev1 ev2
  | MinusA  -> V.add_untyped ~factor:Int_Base.minus_one ev1 ev2
  | MinusPP -> forward_minus_pp ~typ ev1 ev2
  | Mod     -> V.c_rem ev1 ev2
  | Div     -> V.div ev1 ev2
  | Mult    -> V.mul ev1 ev2
  | Shiftrt -> V.shift_right ev1 ev2
  | Shiftlt -> V.shift_left ev1 ev2
  | BXor    -> V.bitwise_xor ev1 ev2
  | BOr     -> V.bitwise_or ev1 ev2
  | BAnd    -> V.bitwise_and ev1 ev2
  (* Strict evaluation. The caller of this function is supposed to take
     into account the laziness of those operators itself *)
  | LOr  ->
    V.interp_boolean
      ~contains_zero:(V.contains_zero ev1 && V.contains_zero ev2)
      ~contains_non_zero:(V.contains_non_zero ev1 || V.contains_non_zero ev2)
  | LAnd ->
    V.interp_boolean
      ~contains_zero: (V.contains_zero ev1 || V.contains_zero ev2)
      ~contains_non_zero:(V.contains_non_zero ev1 && V.contains_non_zero ev2)
  | Eq | Ne | Ge | Le | Gt | Lt ->
    let op = Eva_utils.conv_comp op in
    let signed = Bit_utils.is_signed_int_enum_pointer (Cil.unrollType typ) in
    V.inject_comp_result (V.forward_comp_int ~signed op ev1 ev2)

let forward_binop_float fkind ev1 op ev2 =
  match V.project_float ev1, V.project_float ev2 with
  | exception V.Not_based_on_null ->
    V.join (V.topify_arith_origin ev1) (V.topify_arith_origin ev2)
  | f1, f2 ->
    let binary_float_floats (_name: string) f =
      V.inject_float (f fkind f1 f2)
    in
    match op with
    | PlusA ->   binary_float_floats "+." Fval.add
    | MinusA ->  binary_float_floats "-." Fval.sub
    | Mult ->    binary_float_floats "*." Fval.mul
    | Div ->     binary_float_floats "/." Fval.div
    | Eq | Ne | Lt | Gt | Le | Ge ->
      let op = Eva_utils.conv_comp op in
      V.inject_comp_result (Fval.forward_comp op f1 f2)
    | _ -> assert false


(* --------------------------------------------------------------------------
                       Unary Operators Evaluation
   -------------------------------------------------------------------------- *)

(* This function evaluates a unary minus, but does _not_ check for overflows.
   This is left to the caller *)
let forward_uneg v t =
  try
    match Cil.unrollType t with
    | TFloat _ ->
      let v = V.project_float v in
      V.inject_ival (Ival.inject_float (Fval.neg v))
    | _ ->
      let v = V.project_ival v in
      V.inject_ival (Ival.neg_int v)
  with V.Not_based_on_null ->
    if Cvalue.V.is_bottom v
    then v
    else V.topify_arith_origin v

let forward_unop typ op value =
  match op with
  | Neg -> forward_uneg value typ
  | BNot -> begin
      match Cil.unrollType typ with
      | TInt (ik, _) | TEnum ({ekind=ik}, _) ->
        let size = Cil.bitsSizeOfInt ik in
        let signed = Cil.isSigned ik in
        V.bitwise_not ~signed ~size value
      | _ -> assert false
    end
  | LNot ->
    let eq = Abstract_interp.Comp.Eq in
    (* [!c] holds iff [c] is equal to [O] *)
    if Cil.isFloatingType typ then
      try
        let i = V.project_ival value in
        let f = Ival.project_float i in
        V.inject_comp_result (Fval.forward_comp eq f Fval.plus_zero)
      with V.Not_based_on_null -> V.zero_or_one
    else
      let signed = Bit_utils.is_signed_int_enum_pointer typ in
      V.inject_comp_result
        (V.forward_comp_int ~signed eq value V.singleton_zero)

(* --------------------------------------------------------------------------
                                  Cast
   -------------------------------------------------------------------------- *)

(* Re-export type here *)
type scalar_typ = Eval_typ.scalar_typ =
  | TSInt of integer_range
  | TSPtr of integer_range
  | TSFloat of fkind

let reinterpret_as_int range v =
  let size = Integer.of_int range.i_bits in
  Cvalue.V.reinterpret_as_int ~signed:range.i_signed ~size v

let reinterpret typ v =
  match Eval_typ.classify_as_scalar typ with
  | Some (TSInt ik | TSPtr ik)  -> reinterpret_as_int ik v
  | Some (TSFloat fk) -> Cvalue.V.reinterpret_as_float fk v
  | None -> v

(* Cast from floating-point to integer. [context] is the expression being cast
   and its size, to build the alarms. *)
let cast_float_to_int irange v =
  let size = irange.i_bits in
  let signed = irange.i_signed in
  Cvalue.V.cast_float_to_int ~signed ~size v

let forward_cast ~src_type ~dst_type v =
  match src_type, dst_type with
  | TSFloat _, TSFloat dst -> Cvalue.V.cast_float_to_float (Fval.kind dst) v
  | TSFloat _, (TSInt dst | TSPtr dst) -> cast_float_to_int dst v
  | (TSInt _ | TSPtr _), TSFloat dst ->
    Cvalue.V.cast_int_to_float (Fval.kind dst) v
  | (TSInt _ | TSPtr _), (TSInt _ | TSPtr _) -> v

(* --------------------------------------------------------------------------
                                  Misc
   -------------------------------------------------------------------------- *)

let make_volatile ?typ v =
  let is_volatile = match typ with
    | None -> true
    | Some typ -> Cil.typeHasQualifier "volatile" typ
  in
  if is_volatile && not (V.is_bottom v)
  then
    match v with
    | V.Top _ -> v
    | V.Map m ->
      let aux b _ acc = V.join acc (V.inject b Ival.top) in
      V.M.fold aux m V.bottom
  else v

let eval_float_constant f fkind fstring =
  if Fc_float.is_nan f
  then V.inject_float Fval.nan
  else
    let all_rounding = Parameters.AllRoundingModesConstants.get in
    let fl, fu = match fstring with
      | Some "INFINITY" -> f, f (* Special case for the INFINITY macro. *)
      | Some string when fkind = Cil_types.FLongDouble || all_rounding () ->
        let open Floating_point in
        let {f_lower; f_upper} = snd (parse string) in
        (* Computations are done in double. For long double constants, if we
           reach infinity, we must use the interval [max_double..infty] to be
           sound. Here we even use [-infty..infty]. *)
        if Fc_float.is_infinite f_lower && Fc_float.is_infinite f_upper
        then
          begin
            Eva_utils.warning_once_current
              "cannot parse floating-point constant, returning imprecise result";
            neg_infinity, infinity
          end
        else f_lower, f_upper
      | None | Some _ -> f, f
    in
    let fl = Fval.F.of_float fl
    and fu = Fval.F.of_float fu in
    let af = Fval.inject (Fval.kind fkind) fl fu in
    V.inject_float af


(*
Local Variables:
compile-command: "make -C ../../../.."
End:
*)
