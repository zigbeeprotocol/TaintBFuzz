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

open Numerors_utils

module P = Precisions

(* Type declaration *)
type t = P.t * Mpfr.mpfr_float

(* Pretty printer *)
let pretty fmt (_, f) =
  let (s,e) = Mpfr.get_str ~base:10 ~size:0 f ~rnd:Mpfr.To_Nearest in
  if not (Mpfr.number_p f) then Format.fprintf fmt "%s" s
  else if s = "" then Format.fprintf fmt "0."
  else if s.[0] = '-'
  then Format.fprintf fmt "-0.%sE%s" String.(sub s 1 (length s - 1)) e
  else Format.fprintf fmt "0.%sE%s" s e

(* Get back the MPFR rounding mode *)
let rounding = function
  | Rounding.Near -> Mpfr.To_Nearest
  | Rounding.Down -> Mpfr.Toward_Minus_Infinity
  | Rounding.Up   -> Mpfr.Toward_Plus_Infinity

(*-----------------------------------------------------------------------------
 *    Internal functions to handle the precisions of MPFR numbers
 *---------------------------------------------------------------------------*)

(* Internal : change the precision *)
let change_prec ?(rnd = Mpfr.To_Nearest) prec (p, x) =
  if not (P.eq p prec) then
    Mpfr.make_from_mpfr ~prec:(P.get prec) ~rnd x
  else x
[@@inline]

(* Returns a function which apply the rounding of its optionnal parameter rnd
   and change the precision according to its optionnal parameter prec before
   calling the unary function f on an input of type t *)
let unary_mpfrf (f:?rnd:Mpfr.mpfr_rnd_t -> ?prec:int -> Mpfr.mpfr_float -> Mpfr.mpfr_float) =
  fun ?(rnd = Rounding.Near) ?(prec = P.Real) x ->
  prec, f ~rnd:(rounding rnd) ~prec:(P.get prec) (change_prec prec x)

(* Returns a function which apply the rounding of its optionnal parameter rnd
   and change the precision according to its optionnal parameter prec before
   calling the binary function f on two inputs of type t *)
let binary_mpfrf (f :?rnd:Mpfr.mpfr_rnd_t -> ?prec:int -> Mpfr.mpfr_float -> Mpfr.mpfr_float -> Mpfr.mpfr_float) =
  fun ?(rnd = Rounding.Near) ?(prec = P.Real) x y ->
  prec, f ~rnd:(rounding rnd)  ~prec:(P.get prec) (change_prec prec x) (change_prec prec y)


(*-----------------------------------------------------------------------------
 *    Constructors
 *---------------------------------------------------------------------------*)
let of_int    ?(rnd = Rounding.Near) ?(prec = P.Real) i =
  prec, Mpfr.make_from_int  ~prec:(P.get prec)  i ~rnd:(rounding rnd)

let of_float  ?(rnd = Rounding.Near) ?(prec = P.Real) f =
  prec, Mpfr.make_from_float f ~rnd:(rounding rnd) ~prec:(P.get prec)

let of_string ?(rnd = Rounding.Near) ?(prec = P.Real) str =
  let l = String.length str - 1 in
  let last = Char.lowercase_ascii str.[l] in
  let str =
    if last = 'f' || last = 'd' || last = 'l'
    then String.sub str 0 l
    else str
  in
  (* base is not given to let Mpfr infer the base, depending of the encoding of s. *)
  prec, Mpfr.make_from_str ~prec:(P.get prec) str ~rnd:(rounding rnd)

let pos_zero prec = of_float ~prec 0.0
let neg_zero prec = of_float ~prec (~-. 0.0)

let pos_inf prec = prec, Mpfr.make_from_float infinity      ~rnd:Mpfr.To_Nearest ~prec:(P.get prec)
let neg_inf prec = prec, Mpfr.make_from_float neg_infinity  ~rnd:Mpfr.To_Nearest ~prec:(P.get prec)


(*-----------------------------------------------------------------------------
 *    Comparison methods
 *---------------------------------------------------------------------------*)
let compare (px, nx) (py, ny) =
  if not (Precisions.eq px py) then
    Self.fatal
      "Numerors: impossible to compare two numbers with different precisions"
  else Mpfr.cmp nx ny
let eq a b = compare a b =  0
let le a b = compare a b <= 0
let lt a b = compare a b <  0
let ge a b = compare a b >= 0
let gt a b = compare a b >  0

let min x y = if compare x y <= 0 then x else y
let max x y = if compare x y <= 0 then y else x


(*-----------------------------------------------------------------------------
 *    Getters on floats
 *---------------------------------------------------------------------------*)
let sign (_, x) =
  match Mpfr.sgn x with
  | Positive -> Sign.Positive
  | Negative -> Sign.Negative

let prec (p, _) = p

(* The minus 1 is mandatory because MPFR represents the float numbers
   with a significand between 0 and 1 in place of the standard in the
   IEEE-754 norm. This difference implies that the exponent of the
   MPFR representation is greater than the one of the standard
   representation by one. *)
let exponent (prec, x as f) =
  if eq f (pos_zero prec) then min_int
  else (Mpfr.get_exp x) - 1

let significand (prec, x) =
  let significand = Mpfr.set_exp x 1 in
  prec, Mpfr.abs significand ~rnd:Mpfr.To_Nearest ~prec:(P.get prec)


(*-----------------------------------------------------------------------------
 *    Methods to check properties on floats
 *---------------------------------------------------------------------------*)
let is_nan (_, x) = Mpfr.nan_p x
let is_inf (_, x) = Mpfr.inf_p x

let is_pos f = Sign.is_pos (sign f)
let is_neg f = Sign.is_neg (sign f)

let is_a_zero (prec, _ as f) =  eq f @@ pos_zero prec
let is_pos_zero f = is_pos f && is_a_zero f
let is_neg_zero f = is_neg f && is_a_zero f
let is_strictly_pos f = is_pos f && not (is_a_zero f)
let is_strictly_neg f = is_neg f && not (is_a_zero f)


(*-----------------------------------------------------------------------------
 *    Functions without rounding errors
 *---------------------------------------------------------------------------*)
let neg (p, x) = p, Mpfr.neg x ~rnd:Mpfr.To_Nearest  ~prec:(P.get p)
let abs (p, x) = p, Mpfr.abs x ~rnd:Mpfr.To_Nearest  ~prec:(P.get p)


(*-----------------------------------------------------------------------------
 *    Operators
 *---------------------------------------------------------------------------*)
let add = binary_mpfrf Mpfr.add
let sub = binary_mpfrf Mpfr.sub
let mul = binary_mpfrf Mpfr.mul
let div = binary_mpfrf Mpfr.div
let pow = binary_mpfrf Mpfr.pow
let pow_int =
  fun ?(rnd = Rounding.Near) ?(prec = P.Real) x n ->
  prec, Mpfr.pow_int (change_prec prec x) n ~rnd:(rounding rnd) ~prec:(P.get prec)


(*-----------------------------------------------------------------------------
 *    Functions with rounding errors
 *---------------------------------------------------------------------------*)
let square = unary_mpfrf (fun ?rnd ?prec x -> Mpfr.mul ?rnd ?prec x x)
let sqrt = unary_mpfrf Mpfr.sqrt
let log = unary_mpfrf @@ Mpfr.log
let exp = unary_mpfrf @@ Mpfr.exp
let sin = unary_mpfrf @@ Mpfr.sin
let cos = unary_mpfrf @@ Mpfr.cos
let tan = unary_mpfrf @@ Mpfr.tan


(*-----------------------------------------------------------------------------
 *    Apply the sign of <src> on <dst>
 *---------------------------------------------------------------------------*)
let apply_sign ~src ~dst =
  if not (Sign.eq (sign src) (sign dst)) then neg dst else dst


(*-----------------------------------------------------------------------------
 *    Next and prev float
 *---------------------------------------------------------------------------*)
let next_float (p, x) =
  p, Mpfr.nextabove x

let prev_float (p, x) =
  p, Mpfr.nextbelow x


(*-----------------------------------------------------------------------------
 *    Machine constants
 *---------------------------------------------------------------------------*)
let machine_epsilon ?(prec = P.Real) p =
  pow_int ~rnd:Rounding.Up ~prec (of_int ~prec 2) (- P.get p)

let machine_delta ?(prec = P.Real) p =
  pow_int ~rnd:Rounding.Up ~prec (of_int ~prec 2) @@ (P.denormalized p) - 1

let maximal_pos_float ~prec = prev_float @@ pos_inf prec

let maximal_neg_float ~prec = next_float @@ neg_inf prec

let change_prec ~rnd ~prec t = prec, change_prec ~rnd:(rounding rnd) prec t
