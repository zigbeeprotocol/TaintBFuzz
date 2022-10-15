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

(* Syntactic substitution of globals, defined with the attribute 'const', with
   respective initializers. *)

open Cil_types
open Cil_datatype
open Cil

class constGlobSubstVisitorClass : cilVisitor = object
  inherit nopCilVisitor

  val vi_to_init_opt = Varinfo.Hashtbl.create 7

  (* Visit globals and register only the association between globals with attribute
     'const' and respective initializers. *)
  method! vglob g =
    let rec is_arithmetic_type = function
      | TArray (typ, _, _) -> is_arithmetic_type typ
      | TInt _ | TFloat _ | TEnum _ -> true
      | _ -> false
    in
    match g with
    | GVar (vi, _, _) ->
      (* Register in [vi_to_init_opt] the association between [vi] and its
         initializer [init_opt]. The latter is assumed to be an expression of
         literal constants only, as the lvals originally appearing in it have
         been substituted by the respective initializers in method [vexpr]. *)
      let register = function
        | GVar (vi, { init = init_opt }, _loc) as g ->
          Varinfo.Hashtbl.add vi_to_init_opt vi init_opt;
          g
        | _ ->
          (* Cannot happen as we treat only [GVar _] cases in the outer
             pattern matching. *)
          assert false
      in
      let typ = unrollTypeDeep vi.vtype in
      if is_arithmetic_type typ && isConstType typ
      then ChangeDoChildrenPost ([g], List.map register)
      else DoChildren
    | GFun _ -> DoChildren
    | _ -> SkipChildren

  (* Visit expressions and replace lvals, with a registered varinfo in
     [vi_to_init_opt], with respective initializing constant expressions. *)
  method! vexpr e =
    match e.enode with
    | Lval (Var vi, (NoOffset | Index _ as offset)) ->
      (* Support for variables and array, on arithmetic types only. *)
      begin match Varinfo.Hashtbl.find vi_to_init_opt vi with
        | None ->
          (* Since [vi] is a global, we replace it with the zero expression,
             i.e. the implicit initializer for such globals. *)
          let newexp = zero ~loc:e.eloc in
          ChangeTo newexp
        | Some init ->
          let offset = constFoldOffset true offset in
          let zero_exp = zero ~loc:e.eloc in
          let rec find_replace current_offset current_init current_newexp =
            match current_init with
            | SingleInit si ->
              if Cil_datatype.OffsetStructEq.equal offset current_offset
              then new_exp ~loc:e.eloc si.enode
              else current_newexp
            | CompoundInit (ct, initl) ->
              (* We are dealing with an array: recursively [find_replace] among
                 its initializers. *)
              foldLeftCompound
                ~implicit:true
                ~doinit:(fun coffset cinit _ acc ->
                    find_replace
                      (addOffset coffset current_offset)
                      cinit
                      acc)
                ~ct
                ~initl
                ~acc:current_newexp
          in
          let newexp = find_replace NoOffset init zero_exp in
          ChangeTo newexp
        | exception Not_found ->
          DoChildren
      end
    | _ ->
      DoChildren

  method! vtype _ = Cil.SkipChildren
  method! vspec _ = Cil.SkipChildren
  method! vcode_annot _ = Cil.SkipChildren
end

let constGlobSubstVisitor = new constGlobSubstVisitorClass
