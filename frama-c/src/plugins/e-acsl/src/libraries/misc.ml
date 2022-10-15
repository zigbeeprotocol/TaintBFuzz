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

(* ************************************************************************** *)
(** {2 Handling the E-ACSL's C-libraries, part I} *)
(* ************************************************************************** *)

let is_fc_or_compiler_builtin vi =
  Cil_builtins.is_builtin vi
  ||
  (let prefix_length = 10 (* number of characters in "__builtin_" *) in
   String.length vi.vname > prefix_length
   &&
   let prefix = String.sub vi.vname 0 prefix_length in
   Datatype.String.equal prefix "__builtin_")
  ||
  (Options.Replace_libc_functions.get ()
   && Functions.Libc.has_replacement vi.vname)

let is_fc_stdlib_generated vi =
  Cil.hasAttribute "fc_stdlib_generated" vi.vattr

(* ************************************************************************** *)
(** {2 Handling \result} *)
(* ************************************************************************** *)

let result_lhost kf =
  let stmt =
    try Kernel_function.find_return kf
    with Kernel_function.No_Statement -> assert false
  in
  match stmt.skind with
  | Return(Some { enode = Lval (lhost, NoOffset) }, _) -> lhost
  | _ -> assert false

let result_vi kf = match result_lhost kf with
  | Var vi -> vi
  | Mem _ -> assert false

(* ************************************************************************** *)
(** {2 Other stuff} *)
(* ************************************************************************** *)

let strip_casts e =
  let rec aux casts e =
    match e.enode with
    | CastE(ty, e') -> aux (ty :: casts) e'
    | _ -> e, casts
  in
  aux [] e

let rec add_casts tys e =
  match tys with
  | [] -> e
  | newt :: tl ->
    let e = Cil.mkCast ~newt e in
    add_casts tl e

let cty = function
  | Ctype ty -> ty
  | lty -> Options.fatal "Expecting a C type. Got %a" Printer.pp_logic_type lty

(* Replace all trailing array subscripts of an lval with zero indices. *)
let rec shift_offsets lv loc =
  let lv, off = Cil.removeOffsetLval lv in
  match off with
  | Index _ ->
    let lv = shift_offsets lv loc in
    (* since the offset has been removed at the start of the function, add a new
       0 offset to preserve the type of the lvalue. *)
    Cil.addOffsetLval (Index (Cil.zero ~loc, NoOffset)) lv
  | NoOffset | Field _ -> Cil.addOffsetLval off lv

let rec ptr_base ~loc exp =
  match exp.enode with
  | BinOp(op, lhs, _, _) ->
    (match op with
     (* Pointer arithmetic: split pointer and integer parts *)
     | MinusPI | PlusPI -> ptr_base ~loc lhs
     (* Other arithmetic: treat the whole expression as pointer address *)
     | MinusPP | PlusA | MinusA | Mult | Div | Mod
     | BAnd | BXor | BOr | Shiftlt | Shiftrt
     | Lt | Gt | Le | Ge | Eq | Ne | LAnd | LOr -> exp)
  (* AddressOf: if it is an addressof array then replace all trailing offsets
     with zero offsets to get the base. *)
  | AddrOf lv -> Cil.mkAddrOf ~loc (shift_offsets lv loc)
  (* StartOf already points to the start of an array, return exp directly *)
  | StartOf _ -> exp
  (* Cast: strip cast and continue, then recast to original type. *)
  | CastE _ ->
    let exp, casts = strip_casts exp in
    let base = ptr_base ~loc exp in
    add_casts casts base
  | Const _ | Lval _ | UnOp _ -> exp
  | SizeOf _ | SizeOfE _ | SizeOfStr _ | AlignOf _ | AlignOfE _
    -> assert false

let ptr_base_and_base_addr ~loc e =
  let rec ptr_base_addr ~loc base =
    match base.enode with
    | AddrOf _ | StartOf _ | Const _ -> Cil.zero ~loc
    | Lval lv -> Cil.mkAddrOrStartOf ~loc lv
    | CastE _ -> ptr_base_addr ~loc (Cil.stripCasts base)
    | _ -> assert false
  in
  let base = ptr_base ~loc e in
  let base_addr  = ptr_base_addr ~loc base in
  base, base_addr

(* TODO: should not be in this file *)
let term_of_li li =  match li.l_body with
  | LBterm t -> t
  | LBnone | LBreads _ | LBpred _ | LBinductive _ ->
    Options.fatal "li.l_body does not match LBterm(t) in Misc.term_of_li"

let is_set_of_ptr_or_array lty =
  if Logic_const.is_set_type lty then
    let lty = Logic_const.type_of_element lty in
    Logic_utils.isLogicPointerType lty || Logic_utils.isLogicArrayType lty
  else
    false

exception Range_found_exception
let is_range_free t =
  try
    let has_range_visitor = object inherit Visitor.frama_c_inplace
      method !vterm t = match t.term_node with
        | Trange _ -> raise Range_found_exception
        | _ -> Cil.DoChildren
    end
    in
    ignore (Visitor.visitFramacTerm has_range_visitor t);
    true
  with Range_found_exception ->
    false

let is_bitfield_pointers lty =
  let is_bitfield_pointer = function
    | Ctype typ ->
      begin match Cil.unrollType typ with
        | TPtr(typ, _) ->
          let attrs = Cil.typeAttrs typ in
          Cil.hasAttribute Cil.bitfield_attribute_name attrs
        | _ ->
          false
      end
    | Ltype _ | Lvar _ | Linteger | Lreal | Larrow _ ->
      false
  in
  if Logic_const.is_set_type lty then
    is_bitfield_pointer (Logic_const.type_of_element lty)
  else
    is_bitfield_pointer lty

exception Lv_from_vi_found
let term_has_lv_from_vi t =
  try
    let o = object inherit Visitor.frama_c_inplace
      method !vlogic_var_use lv = match lv.lv_origin with
        | None -> Cil.DoChildren
        | Some _ -> raise Lv_from_vi_found
    end
    in
    ignore (Visitor.visitFramacTerm o t);
    false
  with Lv_from_vi_found ->
    true

let finite_min_and_max i = match Ival.min_and_max i with
  | Some min, Some max -> min, max
  | None, _ | _, None -> assert false

let name_of_binop = function
  | Lt -> "lt"
  | Gt -> "gt"
  | Le -> "le"
  | Ge -> "ge"
  | Eq -> "eq"
  | Ne -> "ne"
  | LOr -> "or"
  | LAnd -> "and"
  | BOr -> "bor"
  | BXor -> "bxor"
  | BAnd -> "band"
  | Shiftrt -> "shiftr"
  | Shiftlt -> "shiftl"
  | Mod -> "mod"
  | Div -> "div"
  | Mult -> "mul"
  | PlusA -> "add"
  | MinusA -> "sub"
  | MinusPP | MinusPI | PlusPI -> assert false

module Id_term =
  Datatype.Make_with_collections
    (struct
      include Cil_datatype.Term
      let name = "E_ACSL.Id_term"
      let compare (t1:term) t2 =
        if t1 == t2 then 0 else Cil_datatype.Term.compare t1 t2
      let equal (t1:term) t2 = t1 == t2
      let structural_descr = Structural_descr.t_abstract
      let rehash = Datatype.identity
      let mem_project = Datatype.never_any_project
    end)

let extract_uncoerced_lval e =
  let rec aux e =
    match e.enode with
    | Lval _ -> Some e
    | CastE (_, e) -> aux e
    | _ -> None
  in
  aux e

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
