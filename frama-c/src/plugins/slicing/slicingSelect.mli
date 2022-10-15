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

val check_call : Cil_types.stmt -> bool -> Cil_types.stmt

val print_select :
  Format.formatter ->
  SlicingTypes.sl_select -> unit

val get_select_kf : Cil_types.varinfo * 'a -> Cil_types.kernel_function

val check_db_select :
  Cil_datatype.Varinfo.t ->
  SlicingTypes.sl_select ->
  SlicingTypes.sl_select

val empty_db_select :
  Kernel_function.t -> Cil_types.varinfo * SlicingInternals.fct_user_crit

val top_db_select :
  Kernel_function.t ->
  SlicingInternals.pdg_mark ->
  Cil_types.varinfo * SlicingInternals.fct_user_crit

val check_kf_db_select :
  Kernel_function.t ->
  SlicingTypes.sl_select ->
  SlicingTypes.sl_select

val check_ff_db_select :
  SlicingInternals.fct_slice ->
  SlicingTypes.sl_select ->

  SlicingTypes.sl_select
val bottom_msg : Kernel_function.t -> unit

val basic_add_select :
  Kernel_function.t ->
  SlicingTypes.sl_select ->
  PdgTypes.Node.t list ->
  ?undef:Locations.Zone.t option * SlicingTypes.sl_mark ->
  SlicingActions.n_or_d_marks ->
  SlicingTypes.sl_select

val select_pdg_nodes :
  Kernel_function.t ->
  ?select:SlicingTypes.sl_select ->
  PdgTypes.Node.t list ->
  SlicingTypes.sl_mark ->
  SlicingTypes.sl_select

val mk_select :
  Db.Pdg.t ->
  SlicingActions.select ->
  (PdgTypes.Node.t * Locations.Zone.t option) list ->
  Locations.Zone.t option ->
  SlicingTypes.sl_mark -> SlicingInternals.fct_user_crit

val select_stmt_zone :
  Kernel_function.t ->
  ?select:SlicingTypes.sl_select ->
  Cil_types.stmt ->
  before:bool ->
  Locations.Zone.t ->
  SlicingTypes.sl_mark ->
  SlicingTypes.sl_select

(** this one is similar to [select_stmt_zone] with the return statement
 * when the function is defined, but it can also be used for undefined functions. *)
val select_in_out_zone :
  at_end:bool ->
  use_undef:bool ->
  Kernel_function.t ->
  SlicingTypes.sl_select ->
  Locations.Zone.t ->
  SlicingTypes.sl_mark ->
  SlicingTypes.sl_select

val select_zone_at_end :
  Kernel_function.t ->
  ?select:SlicingTypes.sl_select ->
  Locations.Zone.t ->
  SlicingTypes.sl_mark ->
  SlicingTypes.sl_select

val select_modified_output_zone :
  Kernel_function.t ->
  ?select:SlicingTypes.sl_select ->
  Locations.Zone.t ->
  SlicingTypes.sl_mark ->
  SlicingTypes.sl_select

val select_zone_at_entry :
  Kernel_function.t ->
  ?select:SlicingTypes.sl_select ->
  Locations.Zone.t ->
  SlicingTypes.sl_mark ->
  SlicingTypes.sl_select

val stmt_nodes_to_select :
  Db.Pdg.t -> Cil_types.stmt -> PdgTypes.Node.t list

val select_stmt_computation :
  Kernel_function.t ->
  ?select:SlicingTypes.sl_select ->
  Cil_types.stmt ->
  SlicingTypes.sl_mark ->
  SlicingTypes.sl_select

val select_label :
  Kernel_function.t ->
  ?select:SlicingTypes.sl_select ->
  Cil_types.logic_label ->
  SlicingTypes.sl_mark ->
  SlicingTypes.sl_select

(** marking a call node means that a [choose_call] will have to decide that to
 * call according to the slicing-level, but anyway, the call will be visible.
*)
val select_minimal_call :
  Kernel_function.t ->
  ?select:SlicingTypes.sl_select ->
  Cil_types.stmt ->
  SlicingTypes.sl_mark ->
  SlicingTypes.sl_select

val select_stmt_ctrl :
  Kernel_function.t ->
  ?select:SlicingTypes.sl_select ->
  Cil_types.stmt -> SlicingTypes.sl_select

val select_entry_point :
  Kernel_function.t ->
  ?select:SlicingTypes.sl_select ->
  SlicingTypes.sl_mark ->
  SlicingTypes.sl_select

val select_return :
  Kernel_function.t ->
  ?select:SlicingTypes.sl_select ->
  SlicingTypes.sl_mark ->
  SlicingTypes.sl_select

val select_decl_var :
  Kernel_function.t ->
  ?select:SlicingTypes.sl_select ->
  Cil_types.varinfo ->
  SlicingTypes.sl_mark ->
  SlicingTypes.sl_select

val merge_select :
  SlicingInternals.fct_user_crit ->
  SlicingInternals.fct_user_crit -> SlicingInternals.fct_user_crit

val merge_db_select :
  SlicingTypes.sl_select ->
  SlicingTypes.sl_select ->
  SlicingTypes.sl_select

module Selections : sig

  val add_to_selects :
    Cil_datatype.Varinfo.Map.key * SlicingInternals.fct_user_crit ->
    SlicingInternals.fct_user_crit Cil_datatype.Varinfo.Map.t ->
    SlicingInternals.fct_user_crit Cil_datatype.Varinfo.Map.t

  val iter_selects_internal :
    (Cil_datatype.Varinfo.Map.key * 'a -> unit) ->
    'a Cil_datatype.Varinfo.Map.t -> unit

  val fold_selects_internal :
    ('a -> Cil_datatype.Varinfo.Map.key * 'b -> 'a) ->
    'a -> 'b Cil_datatype.Varinfo.Map.t -> 'a
end

val add_crit_ff_change_call :
  SlicingInternals.fct_slice ->
  Cil_types.stmt -> SlicingInternals.called_fct -> unit

(** change the call to call the given slice.
 * This is a user request, so it might be the case that
 * the new function doesn't compute enough outputs :
 * in that case, add outputs first.
*)
val call_ff_in_caller :
  caller:SlicingInternals.fct_slice ->
  to_call:SlicingInternals.fct_slice -> unit

val call_fsrc_in_caller :
  caller:SlicingInternals.fct_slice -> to_call:Kernel_function.t -> unit

val call_min_f_in_caller :
  caller:SlicingInternals.fct_slice ->
  to_call:Cil_types.kernel_function -> unit

val is_already_selected :
  SlicingInternals.fct_slice ->
  SlicingTypes.sl_select -> bool

val add_ff_selection :
  SlicingInternals.fct_slice ->
  SlicingTypes.sl_select -> unit

(** add a persistent selection to the function.
 * This might change its slicing level in order to call slices later on. *)
val add_fi_selection :
  SlicingTypes.sl_select -> unit
