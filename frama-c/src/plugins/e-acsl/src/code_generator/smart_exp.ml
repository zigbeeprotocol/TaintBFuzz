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

let lval ~loc lv =
  Cil.new_exp ~loc (Lval lv)

let deref ~loc lv = lval ~loc (Mem lv, NoOffset)

let subscript ~loc array idx =
  match Misc.extract_uncoerced_lval array with
  | Some { enode = Lval lv } ->
    let subscript_lval = Cil.addOffsetLval (Index(idx, NoOffset)) lv in
    lval ~loc subscript_lval
  | Some _ | None ->
    Options.fatal
      ~current:true
      "Trying to create a subscript on an array that is not an Lval: %a"
      Cil_types_debug.pp_exp
      array

let ptr_sizeof ~loc typ =
  match Cil.unrollType typ with
  | TPtr (t', _) -> Cil.new_exp ~loc (SizeOf t')
  | _ -> assert false

let lnot ~loc e =
  let ty = Cil.typeOf e in
  if not (Cil.isScalarType ty) then
    Options.fatal
      ~current:true
      "Trying to create a logical not on an expression that is not scalar: %a"
      Printer.pp_exp e;
  match Cil.isInteger e with
  | None -> begin
      (* The expression is not an integer constant. Simplify the case where a
         logical not is already present, but otherwise return a new expression
         with the [LNot] operator. *)
      match e.enode with
      | UnOp (LNot, e, _) -> e
      | _ -> Cil.new_exp ~loc (UnOp (LNot, e, Cil.intType))
    end
  | Some i when Integer.equal i Integer.zero ->
    (* The expression is an integer equal to zero, directly return one. *)
    Cil.one ~loc
  | _ ->
    (* The expression is an integer that is not equal to zero, directly return
       zero. *)
    Cil.zero ~loc

let null ~loc =
  Cil.mkCast ~newt:(TPtr (TVoid [], [])) (Cil.zero ~loc)

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
