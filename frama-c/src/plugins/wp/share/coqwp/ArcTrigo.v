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

(* This file is generated by Why3's Coq-realize driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require Reals.R_sqrt.
Require Reals.Rbasic_fun.
Require Reals.Rtrigo_def.
Require Reals.Rtrigo1.
Require Reals.Ratan.
Require BuiltIn.
Require real.Real.
Require real.RealInfix.
Require real.Abs.
Require real.Square.
Require real.Trigonometry.

(* Why3 goal *)
Definition asin : R -> R.
Admitted.

(* Why3 goal *)
Definition acos : R -> R.
Admitted.

(* Why3 goal *)
Lemma Sin_asin :
  forall (x:R), (((-1%R)%R <= x)%R /\ (x <= 1%R)%R) ->
  ((Reals.Rtrigo_def.sin (asin x)) = x).
Admitted.

(* Why3 goal *)
Lemma Cos_acos :
  forall (x:R), (((-1%R)%R <= x)%R /\ (x <= 1%R)%R) ->
  ((Reals.Rtrigo_def.cos (acos x)) = x).
Admitted.

