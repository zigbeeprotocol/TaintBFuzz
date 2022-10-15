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

include Plugin.Register
    (struct
      let name = "Eva"
      let shortname = "eva"
      let help =
        "automatically computes variation domains for the variables of the program"
    end)

let () =
  add_plugin_output_aliases ~visible:false ~deprecated:true [ "value" ; "val" ]

(* Do not add dependencies to Kernel parameters here, but at the top of
   Parameters. *)
let kernel_dependencies =
  [ Ast.self;
    Alarms.self;
    Annotations.code_annot_state; ]

let dependencies = Db.Value.self :: kernel_dependencies

let proxy = State_builder.Proxy.(create "eva" Forward dependencies)
let state = State_builder.Proxy.get proxy

let () = State_builder.Proxy.extend [state] Db.Value.proxy


(* Current state of the analysis *)
type computation_state = NotComputed | Computing | Computed | Aborted

module ComputationState =
struct
  let to_string = function
    | NotComputed -> "NotComputed"
    | Computing -> "Computing"
    | Computed -> "Computed"
    | Aborted -> "Aborted"

  module Prototype =
  struct
    include Datatype.Serializable_undefined
    type t = computation_state
    let name = "Eva.Analysis.ComputationState"
    let pretty fmt s = Format.pp_print_string fmt (to_string s)
    let reprs = [ NotComputed ; Computing ; Computed ; Aborted ]
    let dependencies = [ state ]
    let default () = NotComputed
  end

  module Datatype' = Datatype.Make (Prototype)
  module Hook = Hook.Build (Prototype)
  include (State_builder.Ref (Datatype') (Prototype))

  let set s = set s; Hook.apply s
  let () = add_hook_on_update (fun r -> Hook.apply !r)
end

let is_computed () =
  match ComputationState.get () with
  | Computed | Aborted -> true
  | NotComputed | Computing -> false

let current_computation_state = ComputationState.get
let set_computation_state = ComputationState.set

(* Register a hook on current computation state *)
let register_computation_hook ?on f =
  let f' = match on with
    | None -> f
    | Some s -> fun s' -> if s = s' then f s
  in
  ComputationState.Hook.extend f'


(* Debug categories. *)
let dkey_initial_state = register_category "initial-state"
let dkey_final_states = register_category "final-states"
let dkey_summary = register_category "summary"
let dkey_pointer_comparison = register_category "pointer-comparison"
let dkey_cvalue_domain = register_category "d-cvalue"
let dkey_incompatible_states = register_category "incompatible-states"
let dkey_iterator = register_category "iterator"
let dkey_callbacks = register_category "callbacks"
let dkey_widening = register_category "widening"
let dkey_recursion = register_category "recursion"

let () =
  let activate dkey = add_debug_keys dkey in
  List.iter activate
    [dkey_initial_state; dkey_final_states; dkey_summary; dkey_cvalue_domain;
     dkey_recursion; ]

(* Warning categories. *)
let wkey_alarm = register_warn_category "alarm"
let wkey_locals_escaping = register_warn_category "locals-escaping"
let wkey_garbled_mix = register_warn_category "garbled-mix"
let () = set_warn_status wkey_garbled_mix Log.Winactive
let wkey_builtins_missing_spec = register_warn_category "builtins:missing-spec"
let wkey_builtins_override = register_warn_category "builtins:override"
let wkey_libc_unsupported_spec = register_warn_category "libc:unsupported-spec"
let wkey_loop_unroll_auto = register_warn_category "loop-unroll:auto"
let () = set_warn_status wkey_loop_unroll_auto Log.Wfeedback
let wkey_loop_unroll_partial = register_warn_category "loop-unroll:partial"
let () = set_warn_status wkey_loop_unroll_partial Log.Wfeedback
let wkey_missing_loop_unroll = register_warn_category "loop-unroll:missing"
let () = set_warn_status wkey_missing_loop_unroll Log.Winactive
let wkey_missing_loop_unroll_for = register_warn_category "loop-unroll:missing:for"
let () = set_warn_status wkey_missing_loop_unroll_for Log.Winactive
let wkey_signed_overflow = register_warn_category "signed-overflow"
let wkey_invalid_assigns = register_warn_category "invalid-assigns"
let () = set_warn_status wkey_invalid_assigns Log.Wfeedback
let wkey_experimental = register_warn_category "experimental"
let wkey_unknown_size = register_warn_category "unknown-size"
let wkey_ensures_false = register_warn_category "ensures-false"
