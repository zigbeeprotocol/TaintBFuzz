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

type t =
  | StructOrUnion
  | Array
  | NotAggregate

(** @return the content of the array type if [ty] is an array, or None
    otherwise. *)
let rec get_array_typ_opt ty =
  if Gmp_types.is_t ty then
    (* GMP pointer types are declared as arrays of one element. They are treated
       as a special case here to ensure that they are not considered as arrays.
    *)
    None
  else
    match ty with
    | TNamed (r, _) -> get_array_typ_opt r.ttype
    | TArray (t, eo, a) -> Some (t, eo, a)
    | _ -> None

(** @return true iff the type is an array *)
let is_array ty =
  match get_array_typ_opt ty with
  | Some _ -> true
  | None -> false

let get_t ty =
  if is_array ty then
    Array
  else if Cil.isStructOrUnionType ty then
    StructOrUnion
  else
    NotAggregate
