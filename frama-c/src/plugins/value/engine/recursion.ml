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
open Eval

module Varinfo = Cil_datatype.Varinfo

let mark_unknown_requires kinstr kf funspec =
  let stmt =
    match kinstr with
    | Kglobal -> assert false
    | Kstmt stmt -> stmt
  in
  let emitter = Eva_utils.emitter in
  let status = Property_status.Dont_know in
  let emit_behavior behavior =
    let emit_predicate predicate =
      let ip = Property.ip_of_requires kf Kglobal behavior predicate in
      Statuses_by_call.setup_precondition_proxy kf ip;
      let property = Statuses_by_call.precondition_at_call kf ip stmt in
      Property_status.emit ~distinct:true emitter ~hyps:[] property status
    in
    List.iter emit_predicate behavior.b_requires
  in
  List.iter emit_behavior funspec.spec_behavior

let get_spec kinstr kf =
  let funspec = Annotations.funspec ~populate:false kf in
  if Cil.is_empty_funspec funspec then begin
    Self.error ~current:true
      "@[Recursive call to %a@ without a specification.@ \
       Generating probably incomplete assigns to interpret the call.@ \
       Try to increase@ the %s parameter@ \
       or write a correct specification@ for function %a.@\n%t@]"
      (* note: the "\n" before the pretty print of the stack is required by:
         FRAMAC_SHARE/analysis-scripts/make_wrapper.py
      *)
      Kernel_function.pretty kf
      Parameters.RecursiveUnroll.name
      Kernel_function.pretty kf
      Eva_utils.pp_callstack;
    Cil.CurrentLoc.set (Kernel_function.get_location kf);
    ignore (!Annotations.populate_spec_ref kf funspec);
    Annotations.funspec kf
  end
  else
    let depth = Parameters.RecursiveUnroll.get () in
    let () =
      Self.warning ~once:true ~current:true
        "@[Using specification of function %a@ for recursive calls%s.@ \
         Analysis of function %a@ is thus incomplete@ and its soundness@ \
         relies on the written specification.@]"
        Kernel_function.pretty kf
        (if depth > 0 then Format.asprintf " of depth %i" depth else "")
        Kernel_function.pretty kf
    in
    mark_unknown_requires kinstr kf funspec;
    funspec

(* Find a spec for a function [kf] that begins a recursive call. If [kf]
   has no existing specification, generate (an incorrect) one, and warn
   loudly. *)
let _spec_for_recursive_call kf =
  let initial_spec = Annotations.funspec ~populate:false kf in
  match Cil.find_default_behavior initial_spec with
  | Some bhv when bhv.b_assigns <> WritesAny -> initial_spec
  | _ ->
    let assigns = Infer_annotations.assigns_from_prototype kf in
    let bhv = Cil.mk_behavior ~assigns:(Writes assigns) () in
    let spec = { (Cil.empty_funspec ()) with spec_behavior = [bhv] } in
    Self.error ~once:true
      "@[recursive@ call@ on@ an unspecified@ \
       function.@ Using@ potentially@ invalid@ inferred assigns '%t'@]"
      (fun fmt -> match assigns with
         | [] -> Format.pp_print_string fmt "assigns \\nothing"
         | _ :: _ ->
           Pretty_utils.pp_list ~sep:"@ " Printer.pp_from fmt assigns);
    (* Merge existing spec into our custom one with assigns *)
    Logic_utils.merge_funspec
      ~silent_about_merging_behav:true spec initial_spec;
    spec

let _empty_spec_for_recursive_call kf =
  let typ_res = Kernel_function.get_return_type kf in
  let empty = Cil.empty_funspec () in
  let assigns =
    if Cil.isVoidType typ_res then
      Writes []
    else
      let res = TResult typ_res, TNoOffset in
      let res = Logic_const.term (TLval res) (Ctype typ_res) in
      let res = Logic_const.new_identified_term res in
      Writes [res, From []]
  in
  let bhv = Cil.mk_behavior ~assigns ~name:Cil.default_behavior_name () in
  empty.spec_behavior <- [bhv];
  empty


(* -------------------------------------------------------------------------- *)

module CallDepth =
  Datatype.Pair_with_collections (Kernel_function) (Datatype.Int)
    (struct let module_name = "CallDepth" end)

module VarCopies =
  Datatype.List (Datatype.Pair (Varinfo) (Varinfo))

module VarStack =
  State_builder.Hashtbl
    (CallDepth.Hashtbl)
    (VarCopies)
    (struct
      let name = "Eva.Recursion.VarStack"
      let dependencies = [ Ast.self ]
      let size = 9
    end)

let copy_variable fundec depth varinfo =
  let name = Format.asprintf "\\copy<%s>[%i]" varinfo.vname depth in
  let v = Cil.copyVarinfo varinfo name in
  Cil.refresh_local_name fundec v;
  v

let make_stack (kf, depth) =
  let fundec =
    try Kernel_function.get_definition kf
    with Kernel_function.No_Definition -> assert false
  in
  let vars = Kernel_function.(get_formals kf @ get_locals kf) in
  let copy v = v, copy_variable fundec depth v in
  List.map copy vars

let get_stack kf depth = VarStack.memo make_stack (kf, depth)

let make_recursion call depth =
  let dkey = Self.dkey_recursion in
  Self.feedback ~dkey ~once:true ~current:true
    "@[detected recursive call@ of function %a.@]"
    Kernel_function.pretty call.kf;
  let substitution = get_stack call.kf depth in
  let add_if_copy acc argument =
    match argument.avalue with
    | Copy ({ lval = Var vi, _ }, _) -> Varinfo.Set.add vi acc
    | _ -> acc
  in
  let empty = Varinfo.Set.empty in
  let copied_varinfos = List.fold_left add_if_copy empty call.arguments in
  let may_be_used (vi, _) = vi.vaddrof || Varinfo.Set.mem vi copied_varinfos in
  let substitution, withdrawal = List.partition may_be_used substitution in
  let withdrawal = List.map fst withdrawal in
  let base_of_varinfo (v1, v2) = Base.of_varinfo v1, Base.of_varinfo v2 in
  let list_substitution = List.map base_of_varinfo substitution in
  let base_substitution = Base.substitution_from_list list_substitution in
  let list_withdrawal = List.map Base.of_varinfo withdrawal in
  let base_withdrawal = Base.Hptset.of_list list_withdrawal in
  { depth; substitution; base_substitution; withdrawal; base_withdrawal; }

let make call =
  let is_same_kf (f, _) = Kernel_function.equal f call.kf in
  let previous_calls = List.filter is_same_kf call.callstack in
  let depth = List.length previous_calls in
  if depth > 0
  then Some (make_recursion call depth)
  else None

let revert recursion =
  let revert (v1, v2) = v2, v1 in
  let substitution = List.map revert recursion.substitution in
  let base_of_varinfo (v1, v2) = Base.of_varinfo v1, Base.of_varinfo v2 in
  let list = List.map base_of_varinfo substitution in
  let base_substitution = Base.substitution_from_list list in
  { recursion with substitution; base_substitution; }
