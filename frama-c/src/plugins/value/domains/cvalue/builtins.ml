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

exception Invalid_nb_of_args of int
exception Outside_builtin_possibilities

type builtin_type = unit -> typ * typ list
type cacheable = Eval.cacheable = Cacheable | NoCache | NoCacheCallers

type full_result = {
  c_values: (Cvalue.V.t option * Cvalue.Model.t) list;
  c_clobbered: Base.SetLattice.t;
  c_from: (Function_Froms.froms * Locations.Zone.t) option;
}

type call_result =
  | States of Cvalue.Model.t list
  | Result of Cvalue.V.t list
  | Full of full_result

type builtin = Cvalue.Model.t -> (exp * Cvalue.V.t) list -> call_result

(* Table of all registered builtins; filled by [register_builtin] calls.  *)
let table = Hashtbl.create 17

(* Table binding each kernel function to their builtin for a given analysis.
   Filled at the beginning of each analysis by [prepare_builtins]. *)
let builtins_table = Hashtbl.create 17

module Info = struct
  let name = "Eva.Builtins.BuiltinsOverride"
  let dependencies = [ Self.state ]
end

(** Set of functions overridden by a builtin. *)
module BuiltinsOverride = State_builder.Set_ref (Kernel_function.Set) (Info)

let register_builtin name ?replace ?typ cacheable f =
  Parameters.register_builtin name;
  let builtin = (name, f, cacheable, typ) in
  Hashtbl.replace table name builtin;
  match replace with
  | None -> ()
  | Some fname -> Hashtbl.replace table fname builtin

let is_builtin name =
  try
    let bname, _, _, _ = Hashtbl.find table name in
    name = bname
  with Not_found -> false

let builtin_names_and_replacements () =
  let stand_alone, replacements =
    Hashtbl.fold
      (fun name (builtin_name, _, _, _) (acc1, acc2) ->
         if name = builtin_name
         then name :: acc1, acc2
         else acc1, (name, builtin_name) :: acc2)
      table ([], [])
  in
  List.sort String.compare stand_alone,
  List.sort (fun (name1, _) (name2, _) -> String.compare name1 name2) replacements

let () =
  Cmdline.run_after_configuring_stage
    (fun () ->
       if Parameters.BuiltinsList.get () then begin
         let stand_alone, replacements = builtin_names_and_replacements () in
         Log.print_on_output
           (fun fmt ->
              Format.fprintf fmt "@[*** LIST OF EVA BUILTINS@\n@\n\
                                  ** Replacements set -eva-builtins-auto:\
                                  @\n   unless otherwise specified, \
                                  function <f> is replaced by builtin \
                                  Frama_C_<f>:@\n@\n   @[%a@]@]@\n"
                (Pretty_utils.pp_list ~sep:",@ "
                   (fun fmt (name, rep_by) ->
                      if rep_by = "Frama_C_" ^ name then
                        Format.fprintf fmt "%s" name
                      else
                        Format.fprintf fmt "%s (replaced by: %s)" name rep_by))
                replacements);
         Log.print_on_output
           (fun fmt ->
              Format.fprintf fmt "@\n@[** Full list of builtins \
                                  (configurable via -eva-builtin):@\n\
                                  @\n   @[%a@]@]@\n"
                (Pretty_utils.pp_list ~sep:",@ "
                   Format.pp_print_string) stand_alone);
         raise Cmdline.Exit
       end)

(* -------------------------------------------------------------------------- *)
(* --- Prepare builtins for an analysis                                   --- *)
(* -------------------------------------------------------------------------- *)

(* Returns the specification of a builtin, used to evaluate preconditions
   and to transfer the states of other domains. *)
let find_builtin_specification kf =
  let spec = Annotations.funspec kf in
  (* The specification can be empty if [kf] has a body but no specification,
     in which case [Annotations.funspec] does not generate a specification.
     TODO: check that the specification is the frama-c libc specification? *)
  if spec.spec_behavior <> [] then Some spec else None

(* Returns [true] if the function [kf] is incompatible with the expected type
   for a given builtin, which therefore cannot be applied. *)
let inconsistent_builtin_typ kf = function
  | None -> false (* No expected type provided with the builtin, no check. *)
  | Some typ ->
    let expected_result, expected_args = typ () in
    match Kernel_function.get_type kf with
    | TFun (result, args, _, _) ->
      (* If a builtin expects a void pointer, then accept all pointer types. *)
      let need_cast typ expected =
        Cil.need_cast typ expected
        && not (Cil.isVoidPtrType expected && Cil.isPointerType typ)
      in
      let args = Cil.argsToList args in
      need_cast result expected_result
      || List.length args <> List.length expected_args
      || List.exists2 (fun (_, t, _) u -> need_cast t u) args expected_args
    | _ -> assert false

(* Warns if the builtin [bname] overrides the function definition [kf]. *)
let warn_builtin_override kf source bname =
  let internal =
    (* TODO: treat this 'internal' *)
    let file = source.Filepath.pos_path in
    Filepath.is_relative ~base_name:Fc_config.datadir file
  in
  if Kernel_function.is_definition kf && not internal
  then
    let fname = Kernel_function.get_name kf in
    Self.warning ~source ~once:true
      ~wkey:Self.wkey_builtins_override
      "function %s: definition will be overridden by %s"
      fname (if fname = bname then "its builtin" else "builtin " ^ bname)

let prepare_builtin kf (name, builtin, cacheable, expected_typ) =
  let source = fst (Kernel_function.get_location kf) in
  if inconsistent_builtin_typ kf expected_typ
  then
    Self.warning ~source ~once:true
      ~wkey:Self.wkey_builtins_override
      "The builtin %s will not be used for function %a of incompatible type.@ \
       (got: %a)."
      name Kernel_function.pretty kf
      Printer.pp_typ (Kernel_function.get_type kf)
  else
    match find_builtin_specification kf with
    | None ->
      Self.warning ~source ~once:true
        ~wkey:Self.wkey_builtins_missing_spec
        "The builtin for function %a will not be used, as its frama-c libc \
         specification is not available."
        Kernel_function.pretty kf
    | Some spec ->
      warn_builtin_override kf source name;
      BuiltinsOverride.add kf;
      Hashtbl.replace builtins_table kf (name, builtin, cacheable, spec)

let prepare_builtins () =
  BuiltinsOverride.clear ();
  Hashtbl.clear builtins_table;
  let autobuiltins = Parameters.BuiltinsAuto.get () in
  (* Links kernel functions to the registered builtins. *)
  Hashtbl.iter
    (fun name (bname, f, cacheable, typ) ->
       if autobuiltins || name = bname
       then
         try
           let kf = Globals.Functions.find_by_name name in
           prepare_builtin kf (name, f, cacheable, typ)
         with Not_found -> ())
    table;
  (* Overrides builtins attribution according to the -eva-builtin option. *)
  Parameters.BuiltinsOverrides.iter
    (fun (kf, name) ->
       prepare_builtin kf (Hashtbl.find table (Option.get name)))

let find_builtin_override = Hashtbl.find_opt builtins_table

let is_builtin_overridden name =
  if not (BuiltinsOverride.is_computed ())
  then prepare_builtins ();
  BuiltinsOverride.mem name

(* -------------------------------------------------------------------------- *)
(* --- Applying a builtin                                                 --- *)
(* -------------------------------------------------------------------------- *)

let clobbered_set_from_ret state ret =
  let aux b _ acc =
    match Cvalue.Model.find_base_or_default b state with
    | `Top -> Base.SetLattice.top
    | `Bottom -> acc
    | `Value m ->
      if Locals_scoping.offsetmap_contains_local m then
        Base.SetLattice.(join (inject_singleton b) acc)
      else acc
  in
  try Cvalue.V.fold_topset_ok aux ret Base.SetLattice.bottom
  with Abstract_interp.Error_Top -> Base.SetLattice.top

type call = (Precise_locs.precise_location, Cvalue.V.t) Eval.call
type result = Cvalue.Model.t * Locals_scoping.clobbered_set

open Eval

let compute_arguments arguments rest =
  let compute assigned =
    match Eval.value_assigned assigned with
    | `Bottom -> Cvalue.V.bottom
    | `Value v -> v
  in
  let list = List.map (fun arg -> arg.concrete, compute arg.avalue) arguments in
  let rest = List.map (fun (exp, v) -> exp, compute v) rest in
  list @ rest

let process_result call state call_result =
  let clob = Locals_scoping.bottom () in
  let bind_result state return =
    match return, call.return with
    | Some value, Some vi_ret ->
      let b_ret = Base.of_varinfo vi_ret in
      let offsm = Eval_op.offsetmap_of_v ~typ:vi_ret.vtype value in
      Cvalue.Model.add_base b_ret offsm state, clob
    | _, _ -> state, clob (* TODO: error? *)
  in
  match call_result with
  | States states -> List.rev_map (fun s -> s, clob) states
  | Result values -> List.rev_map (fun v -> bind_result state (Some v)) values
  | Full result ->
    Locals_scoping.remember_bases_with_locals clob result.c_clobbered;
    let process_one_return acc (return, state) =
      if Cvalue.Model.is_reachable state
      then bind_result state return :: acc
      else acc
    in
    List.fold_left process_one_return [] result.c_values

let apply_builtin (builtin:builtin) call ~pre ~post =
  let arguments = compute_arguments call.arguments call.rest in
  try
    let call_result = builtin pre arguments in
    let call_stack = Eva_utils.call_stack () in
    let froms =
      match call_result with
      | Full result -> `Builtin result.c_from
      | States _ -> `Builtin None
      | Result _ -> `Spec (Annotations.funspec call.kf)
    in
    Db.Value.Call_Type_Value_Callbacks.apply (froms, pre, call_stack);
    process_result call post call_result
  with
  | Invalid_nb_of_args n ->
    Self.abort ~current:true
      "Invalid number of arguments for builtin %a: %d expected, %d found"
      Kernel_function.pretty call.kf n (List.length arguments)
  | Outside_builtin_possibilities ->
    Self.fatal ~current:true
      "Call to builtin %a failed" Kernel_function.pretty call.kf

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
