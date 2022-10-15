(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(* --- Weakest Pre Accumulator                                            --- *)
(* -------------------------------------------------------------------------- *)

open Cil_types
open Lang
open Lang.F

(** {2 Predicate Introduction} *)


(** Introduce universally quantified formulae: head forall quantifiers
    are instanciated to fresh variables in current pool and left-implies are
    extracted, recursively. *)
val forall_intro: Lang.F.pred -> Lang.F.pred list * Lang.F.pred

(** Introduce existential quantified formulae: head exist quantifiers
    are instanciated to fresh variables, recursively. *)
val exist_intro: Lang.F.pred -> Lang.F.pred

(** {2 Sequent} *)

type step = private {
  mutable id : int ; (** See [index] *)
  size : int ;
  vars : Vars.t ;
  stmt : stmt option ;
  descr : string option ;
  deps : Property.t list ;
  warn : Warning.Set.t ;
  condition : condition ;
}

and condition =
  | Type of pred (** Type section, not constraining for filtering *)
  | Have of pred (** Normal assumptions section *)
  | When of pred (** Assumptions introduced after simplifications *)
  | Core of pred (** Common hypotheses gather from parallel branches *)
  | Init of pred (** Initializers assumptions *)
  | Branch of pred * sequence * sequence (** If-Then-Else *)
  | Either of sequence list (** Disjunction *)
  | State of Mstate.state (** Memory Model snapshot *)

and sequence (** List of steps *)

type sequent = sequence * F.pred

val pretty : (Format.formatter -> sequent -> unit) ref

(** Creates a single step *)
val step :
  ?descr:string ->
  ?stmt:stmt ->
  ?deps:Property.t list ->
  ?warn:Warning.Set.t ->
  condition -> step

(** Updates the condition of a step and merges [descr], [deps] and [warn] *)
val update_cond :
  ?descr:string ->
  ?deps:Property.t list ->
  ?warn:Warning.Set.t ->
  step ->
  condition -> step

val is_true : sequence -> bool
(** Contains only true or empty steps *)

val is_empty : sequence -> bool
(** No step at all *)

val vars_hyp : sequence -> Vars.t
(** Pre-computed and available in constant time. *)

val vars_seq : sequent -> Vars.t
(** At the cost of the union of hypotheses and goal. *)

val empty : sequence
(** empty sequence, equivalent to true assumption *)

val trivial : sequent
(** empty implies true *)

val sequence : step list -> sequence

val seq_branch : ?stmt:stmt -> F.pred -> sequence -> sequence -> sequence
(** Creates an If-Then-Else branch located at the provided stmt, if any. *)

val append : sequence -> sequence -> sequence (** Conjunction *)

val concat : sequence list -> sequence (** List conjunction *)

(** Iterate only over the head steps of the sequence.
    Does not go deeper inside branches and disjunctions. *)
val iter : (step -> unit) -> sequence -> unit

(** Same domain than [iter]. *)
val list : sequence -> step list

(** Compute the {i total} number of steps in the sequence, including
    nested sequences from branches and disjunctions.
    Pre-computed and available in constant time. *)
val size : sequence -> int

val steps : sequence -> int
(** Attributes unique indices to every [step.id] in the sequence,
    starting from zero. Recursively
    Returns the number of steps in the sequence. *)

val index : sequent -> unit
(** Compute steps' id of sequent left hand-side.
    Same as [ignore (steps (fst s))]. *)

val step_at : sequence -> int -> step
(** Retrieve a step by [id] in the sequence.
    The [index] function {i must} have been called on the sequence before
    retrieving the index properly.
    @raise Not_found if the index is out of bounds. *)

val is_trivial : sequent -> bool
(** Goal is true or hypotheses contains false. *)

(** {2 Transformations} *)

val map_condition : (pred -> pred) -> condition -> condition
(** Rewrite all root predicates in condition *)

val map_step : (pred -> pred) -> step -> step
(** Rewrite all root predicates in step *)

val map_sequence : (pred -> pred) -> sequence -> sequence
(** Rewrite all root predicates in sequence *)

val map_sequent : (pred -> pred) -> sequent -> sequent
(** Rewrite all root predicates in hypotheses and goal *)

val insert : ?at:int -> step -> sequent -> sequent
(** Insert a step in the sequent immediately [at] the specified position.
    Parameter [at] can be [size] to insert at the end of the sequent (default).
    @raise Invalid_argument if the index is out of bounds. *)

val replace : at:int -> step -> sequent -> sequent
(** replace a step in the sequent, the one [at] the specified position.
    @raise Invalid_argument if the index is out of bounds. *)

val replace_by_step_list : at:int -> step list -> sequent -> sequent
(** replace a step in the sequent, the one [at] the specified position.
    @raise Invalid_argument if the index is out of bounds. *)

val subst : (term -> term) -> sequent -> sequent
(** Apply the atomic substitution recursively using [Lang.F.p_subst f].
    Function [f] should only transform the head of the predicate, and can assume
    its sub-terms have been already substituted. The atomic substitution is also applied
    to predicates.
    [f] should raise [Not_found] on terms that must not be replaced
*)

val introduction : sequent -> sequent option
(** Performs existential, universal and hypotheses introductions *)

val introduction_eq : sequent -> sequent
(** Same as [introduction] but returns the same sequent is None *)

val lemma : pred -> sequent
(** Performs existential, universal and hypotheses introductions *)

val head : step -> pred
(** Predicate for Have and such, Condition for Branch, True for Either *)

val have : step -> pred
(** Predicate for Have and such, True for any other *)

val pred_cond : condition -> pred

val condition : sequence -> pred
(** With free variables kept. *)

val close : sequent -> pred
(** With free variables {i quantified}. *)

val at_closure : (sequent -> sequent ) -> unit
(** register a transformation applied just before close *)

(** {2 Bundles}

    Bundles are {i mergeable} pre-sequences.
    This the key structure for merging hypotheses with linear complexity
    during backward weakest pre-condition calculus.

    Bundle are constructed in backward order with respect to program
    control-flow, as driven by the wp calculus.
*)

type bundle

type 'a attributed =
  ( ?descr:string ->
    ?stmt:stmt ->
    ?deps:Property.t list ->
    ?warn:Warning.Set.t ->
    'a )

val nil : bundle (** Same as empty *)

val occurs : F.var -> bundle -> bool
val intersect : F.pred -> bundle -> bool
(** Variables of predicate and the bundle intersects *)

val merge : bundle list -> bundle
(** Performs a diff-based disjunction, introducing If-Then-Else or Either
    branches when possible.
    Linear complexity is achieved by assuming bundle ordering is consistent
    over the list. *)

(** Assumes a list of predicates in a [Type] section on top of the bundle. *)
val domain : F.pred list -> bundle -> bundle

(** Assumes a list of predicates in a [Have] section on top of the bundle. *)
val intros : F.pred list -> bundle -> bundle

(** Stack a memory model state on top of the bundle. *)
val state : ?descr:string -> ?stmt:stmt -> Mstate.state -> bundle -> bundle

(** Assumes a predicate in the specified section,
    with the specified decorations. On [~init:true], the predicate is placed
    in an [Init] section. On [~domain:true], the predicate is placed in a [Type]
    section. Otherwized, it is placed in a standard [Have] section. *)
val assume : (?init:bool -> ?domain:bool -> F.pred -> bundle -> bundle) attributed

(** Construct a branch bundle, with merging of all common parts. *)
val branch : (F.pred -> bundle -> bundle -> bundle) attributed

(** Construct a disjunction bundle, with merging of all common parts. *)
val either : (bundle list -> bundle) attributed

(** Computes a formulae equivalent to the bundle. For debugging purpose only. *)
val extract : bundle -> F.pred list

(** Closes the bundle and promote it into a well-formed sequence. *)
val bundle : bundle -> sequence

(** {2 Simplifiers} *)

val clean : sequent -> sequent
val filter : sequent -> sequent
val parasite : sequent -> sequent
val init_filter : sequent -> sequent
val simplify : ?solvers:simplifier list -> ?intros:int -> sequent -> sequent
val pruning : ?solvers:simplifier list -> sequent -> sequent

(* -------------------------------------------------------------------------- *)
