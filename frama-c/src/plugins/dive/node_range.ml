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

open Dive_types

type t = node_range

let fkind_limits =
  let max_single = float_of_string "0x1.fffffep+127"
  and max_double = float_of_string "0x1.fffffffffffffp+1023" in
  function
  | Cil_types.FFloat -> max_single
  | FDouble | FLongDouble -> max_double

let ikind_limits ikind =
  let open Cil in
  let bits = bitsSizeOfInt ikind in
  if isSigned ikind then
    (min_signed_number bits, max_signed_number bits)
  else
    (Integer.zero, max_unsigned_number bits)

let logscale x limit =
  Float.(to_int (min 100. (100. *. log (max x 1.) /. log limit)))

let log2scale x limit =
  assert (x > 0.);
  assert (limit > 0.);
  Float.(logscale (log x) (log limit))

let interval_range l u limit =
  let range =
    if (l < 0.0) = (u < 0.0) then (* if bounds have same sign *)
      u -. l
    else
      Float.(max (abs u) (abs l))
  in
  let s = log2scale range limit in
  if s > 98 then Wide else Normal s

let integer_range ikind l u =
  let _, limit = ikind_limits ikind
  and l = Integer.to_float l
  and u = Integer.to_float u in
  interval_range l u (Integer.to_float limit)

let float_range fkind l u =
  let limit = fkind_limits fkind
  and l = Fval.F.to_float l
  and u = Fval.F.to_float u in
  interval_range l u limit

let default_range n =
  Normal (logscale (Integer.to_float n) 100.)

let evaluate cvalue typ =
  let cardinal = Cvalue.V.cardinal cvalue in
  match typ, cardinal with
  | _, Some card when Integer.is_zero card -> Empty
  | _, Some card when Integer.is_one card -> Singleton
  | Cil_types.TInt (ikind,_), _ ->
    begin match Ival.min_and_max (Cvalue.V.project_ival cvalue) with
      | Some l, Some u -> integer_range ikind l u
      | _, _ -> Wide
      | exception Cvalue.V.Not_based_on_null -> Wide
      | exception Abstract_interp.Error_Bottom -> Empty
    end
  | Cil_types.TFloat (fkind,_), _ ->
    begin match Ival.min_and_max_float (Cvalue.V.project_ival cvalue) with
      | Some (l, u), _can_be_nan -> float_range fkind l u
      | _, _ -> Wide
      | exception Cvalue.V.Not_based_on_null -> Wide
      | exception Abstract_interp.Error_Bottom -> Empty
    end
  | _, Some cardinal ->
    default_range cardinal
  | _, None ->
    try
      let size = Integer.of_int (Cil.bitsSizeOf typ) in
      if Integer.(le size sixteen)
      then default_range (Integer.two_power size)
      else Wide
    with Cil.SizeOfError _ -> Empty

let upper_bound r1 r2 =
  match r1, r2 with
  | Empty, r | r, Empty -> r
  | Singleton, r | r, Singleton -> r
  | Normal i1, Normal i2 -> Normal (max i1 i2)
  | Wide, _ | _, Wide -> Wide
