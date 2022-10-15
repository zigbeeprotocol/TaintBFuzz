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

(** {2 Internals types}
    Internals type definitions should be hidden to the outside world,
    but it is not really possible to have abstract types since Slicing has to
    use Db.Slicing functions... *)

open Cil_datatype

(** {3 About options} *)

(** associate a level to each function in order to control how it will be
 * specialized. This is only a hint used when the tool has to make a choice,
 * but it doesn't forbid to the user to do whatever he wants
 * (like building slices for a [DontSlice] function). *)
type level_option =
  | DontSlice (** don't build slice for the function :
                  ie. always call the source function. *)
  | DontSliceButComputeMarks
  (** don't slice the called functions,
   *   but compute the marks for them *)
  | MinNbSlice (** try to use existing slices, create at most one *)
  | MaxNbSlice (** most precise slices
                   (but merge slices with the same visibility,
                    even if they don't have the same marks) *)

(** {3 About function slice} *)

(** Kinds of elementary marks. *)
type mark = Cav of PdgTypes.Dpd.t
          | Spare

val compare_mark : mark -> mark -> int

(** Each PDG element has 2 marks to deal with interprocedural propagation *)
type pdg_mark = {m1 : mark ; m2 : mark }

val pdg_mark_packed_descr : Structural_descr.pack

val compare_pdg_mark : pdg_mark -> pdg_mark -> int

(** Type for all the informations related to any function,
 * even if we don't have its definition.  *)
type fct_info = {
  fi_kf : Cil_types.kernel_function;
  fi_def : Cil_types.fundec option;
  mutable fi_top : pdg_mark option;
  (** indicates if the function is marked top (=> src visible) *)
  mutable fi_level_option : level_option;
  (** level of specialisation for this function *)
  mutable fi_init_marks : ff_marks option;
  (** the marks that must be in every slices of that function *)
  mutable fi_slices : fct_slice list ;
  (** the list of the slices already computed for this function. *)
  mutable fi_next_ff_num : int;
  (** the number to assign to the next slice. *)
  mutable f_called_by : called_by;
  (** calls in slices that call source fct *)
}

(** to represent where a function is called. *)
and called_by = (fct_slice * Cil_types.stmt) list

(** Function slice :
      created as soon as there is a criterion to compute it,
      even if the slice itself hasn't been computed yet.
*)
and fct_slice  = {
  ff_fct : fct_info ;
  ff_id : int ;
  mutable ff_marks : ff_marks;
  mutable ff_called_by : called_by
}

(** [fct_id] is used to identify either a source function or a sliced one.*)
and fct_id =
  | FctSrc of fct_info  (** source function *)
  | FctSliced of fct_slice (** sliced function *)

and called_fct =
  | CallSrc of fct_info option
  (** call the source function (might be unknown if the call uses pointer) *)
  | CallSlice of fct_slice

(** information about a call in a slice which gives the function to call *)
and call_info = called_fct option

(** main part of a slice = mapping between the function elements
    and information about them in the slice. *)
and marks_index = (pdg_mark, call_info) PdgIndex.FctIndex.t

and ff_marks = PdgTypes.Pdg.t * marks_index

and project = {
  functions : fct_info Varinfo.Hashtbl.t;
  mutable actions : criterion list;
}

(** Slicing criterion at the application level.
      When applied, they are translated into [fct_criterion]
*)
and appli_criterion =
  | CaGlobalData of Locations.Zone.t
  (** select all that is necessary to compute the given location. *)
  | CaCall of fct_info
  (** select all that is necessary to call the given function.
   * Its application generates requests to add persistent selection
   * to all the function callers. *)
  | CaOther

(** Base criterion for the functions. These are the only one that can
    really generate function slices. All the other criteria are
    translated in more basic ones.
    Note that to build such a base criterion, the PDG has to be already
    computed.
*)
and fct_base_criterion = pdg_mark PdgMarks.select

(** Used to identify a location (zone) at a given program point.
      * The boolean tell if the point is before (true) or after the statement *)
and loc_point = Cil_types.stmt * Locations.Zone.t * bool

(** [node_or_dpds] tells how we want to select nodes,
    or some of their dependencies (see {!fct_user_crit}). *)
and node_or_dpds = CwNode | CwAddrDpds | CwDataDpds | CwCtrlDpds

(** Tells which marks we want to put in the slice of a function *)
and fct_user_crit =
  | CuSelect of pdg_mark PdgMarks.select
  | CuTop of pdg_mark (** the function has probably no PDG,
                          but we nonetheless give a mark to propagate *)

(** kinds of actions that can be apply to a function *)
and fct_crit =
  | CcUserMark of fct_user_crit
  (** add marks to a slice *)
  | CcChooseCall of Cil_types.stmt
  (** have to choose what function to call here. *)
  | CcChangeCall of Cil_types.stmt * called_fct
  (** call the [called_fct] for the given call [Cil_types.stmt] *)
  | CcMissingOutputs of Cil_types.stmt * (pdg_mark PdgMarks.select) * bool
  (** this call is affected to a function that doesn't compute enough
   * outputs : we will have to choose between adding outputs to that slice,
   * or call another one. The boolean tells if the modifications would
   * change the visibility of some outputs. *)
  | CcMissingInputs of Cil_types.stmt * (pdg_mark PdgMarks.select) * bool
  (** the function calls a slice that has been modified :
   * and doesn't compute not enough inputs.
   * We will have to choose between adding marks to this function,
   * and call another slice.
   * The boolean tells if the modifications would
   * change the visibility of some inputs. *)
  | CcPropagate of (pdg_mark PdgMarks.select)
  (** simply propagate the given marks *)
  | CcExamineCalls of pdg_mark PdgMarks.info_called_outputs

(** Slicing criterion for a function.  *)
and fct_criterion =  {
  cf_fct : fct_id ;
  (** Identification of the {b RESULT} of this filter.
   * When it a a slice, it might be an existing slice that will be modified,
    * or a new one will be created during application.
    * When it is the source function, it means what the criterion has to be
    * applied on each existing slice, and stored into the initial marks of
    * the function.
  *)
  cf_info : fct_crit
}

(** A slicing criterion is either an application level criterion,
    or a function level one.  *)
and criterion =
    CrAppli of appli_criterion | CrFct of fct_criterion

(** {2 Internals values} *)

(** {3 For the journalization of these internals types} *)

val dummy_pdg_mark : pdg_mark

val dummy_fct_info : fct_info

val dummy_marks_index : (pdg_mark, call_info) PdgIndex.FctIndex.t

val dummy_ff_marks :
  PdgTypes.Pdg.t * (pdg_mark, call_info) PdgIndex.FctIndex.t

val dummy_fct_slice : fct_slice

val dummy_fct_user_crit : fct_user_crit

(** The whole project. *)
val dummy_project : project
