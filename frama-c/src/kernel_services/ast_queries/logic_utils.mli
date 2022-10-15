(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA   (Commissariat à l'énergie atomique et aux énergies            *)
(*           alternatives)                                                *)
(*    INRIA (Institut National de Recherche en Informatique et en         *)
(*           Automatique)                                                 *)
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

(** Utilities for ACSL constructs.
    @plugin development guide *)

open Cil_types

(** exception raised when a parsed logic expression is
    syntactically not well-formed. *)
exception Not_well_formed of location * string

(** basic utilities for logic terms and predicates. See also {! Logic_const}
    to build terms and predicates.
    @plugin development guide *)

(** add a logic function in the environment.
    See {!Logic_env.add_logic_function_gen}*)
val add_logic_function : logic_info -> unit

(** {2 Types} *)

(** [is_instance_of poly t1 t2] returns [true] if [t1] can be derived from [t2]
    by instantiating some of the type variable in [poly].

    @since Magnesium-20151001
*)
val is_instance_of: string list -> logic_type -> logic_type -> bool

(** expands logic type definitions. If the [unroll_typedef] flag is set to
    [true] (this is the default), C typedef will be expanded as well. *)
val unroll_type : ?unroll_typedef:bool -> logic_type -> logic_type

(** [isLogicType test typ] is [false] for pure logic types and the result
    of test for C types.
    In case of a set type, the function tests the element type.
*)
val isLogicType : (typ -> bool) -> logic_type -> bool

(** {3 Predefined tests over types} *)
val isLogicArrayType : logic_type -> bool

val isLogicCharType : logic_type -> bool

(** @since Chlorine-20180501 *)
val isLogicAnyCharType : logic_type -> bool
val isLogicVoidType : logic_type -> bool
val isLogicPointerType : logic_type -> bool
val isLogicVoidPointerType : logic_type -> bool

(** {3 Type conversions} *)

(** @return the equivalent C type.
    @raise Failure if the type is purely logical *)
val logicCType : logic_type -> typ

(** transforms an array into pointer. *)
val array_to_ptr : logic_type -> logic_type

(** C type to logic type, with implicit conversion for arithmetic types.
    @since 21.0-Scandium
*)
val coerce_type : typ -> logic_type

(** {2 Predicates} *)

(** transforms \old and \at(,Old) into \at(,L) for L a label pointing
    to the given statement, creating one if needed. *)
val translate_old_label: stmt -> predicate -> predicate

(** {2 Terms} *)

(** [true] if the term denotes a C array. *)
val is_C_array : term -> bool

(** creates a TStartOf from an TLval. *)
val mk_logic_StartOf : term -> term

(** creates an AddrOf from a TLval. The given logic type is the
    type of the lval.
    @since Neon-20140301 *)
val mk_logic_AddrOf: ?loc:location -> term_lval -> logic_type -> term

(** [true] if the term is a pointer. *)
val isLogicPointer : term -> bool

(** creates either a TStartOf or the corresponding TLval. *)
val mk_logic_pointer_or_StartOf : term -> term

(** creates a logic cast if required, with some automatic simplifications being
    performed automatically. If [force] is [true], the cast will always
    be inserted. Otherwise (which is the default), [mk_cast typ t] will return
    [t] if it is already of type [typ]
*)
val mk_cast: ?loc:location -> ?force:bool -> typ -> term -> term


(** [array_with_range arr size] returns the logic term [array'+{0..(size-1)}],
    [array'] being [array] cast to a pointer to char *)
val array_with_range: exp -> term -> term

(** Removes TLogic_coerce at head of term. *)
val remove_logic_coerce: term -> term

(** [numeric_coerce typ t] returns a term with the same value as [t]
    and of type [typ].  [typ] which should be [Linteger] or
    [Lreal]. [numeric_coerce] tries to avoid unnecessary type conversions
    in [t]. In particular, [numeric_coerce (int)cst Linteger], where [cst]
    fits in int will be directly [cst], without any coercion.

    Also coerce recursively the sub-terms of t-set expressions
    (range, union, inter and comprehension) and lift the associated
    set type.

    @since Magnesium-20151001
    @before 21.0-Scandium was ambiguous (coercion vs. conversion).
*)
val numeric_coerce: logic_type -> term -> term

(** {2 Predicates} *)

(** \valid_index *)
(* val mk_pvalid_index: ?loc:location -> term * term -> predicate *)

(** \valid_range *)
(* val mk_pvalid_range: ?loc:location -> term * term * term -> predicate *)

val pointer_comparable: ?loc:location -> term -> term -> predicate
(** \pointer_comparable
    @since Fluorine-20130401 *)

(** {2 Conversion from exp to term} *)

val expr_to_term : ?coerce:bool -> exp -> term
(** Returns a logic term that has exactly the same semantics as the
    original C-expression. The type of the resulting term is determined
    by the [~coerce] flag as follows:
    - when [~coerce:false] is given (the default) the term has the same
      c-type as the original expression.
    - when [~coerce:true] is given, if the original expression has an int or
      float type, then the returned term is coerced into the integer or real
      logic type, respectively.

    Remark: when the original expression is a comparison, it is evaluated as
    an [int] or an [integer] depending on the [~coerce] flag.
    To obtain a boolean or predicate, use [expr_to_boolean] or
    [expr_to_predicate] instead.

    @before 21.0-Scandium was unsound in many cases.
*)

val expr_to_predicate: exp -> predicate
(** Returns a predicate semantically equivalent to the condition
    of the original C-expression.

    This is different from [expr_to_term e |> scalar_term_to_predicate]
    since C-relations are translated into logic ones.

    @raise Fatal error if the expression is not a comparison and cannot be
           compared to zero.
    @since Sulfur-20171101
    @before 21.0-Scandium was unsound in many cases.
*)

val expr_to_ipredicate: exp -> identified_predicate
(** Returns a predicate semantically equivalent to the condition
    of the original C-expression.

    Identical to [expr_to_predicate e |> Logic_const.new_predicate].

    @raise Fatal error if the expression is not a comparison and cannot be
           compared to zero.
    @since Sulfur-20171101
    @before 21.0-Scandium was unsound in many cases.
*)

val expr_to_boolean: exp -> term
(** Returns a boolean term semantically equivalent to the condition
    of the original C-expression.

    This is different from [expr_to_term e |> scalar_term_to_predicate]
    since C-relations are translated into logic ones.

    @raise Fatal error if the expression is not a comparison and cannot be
           compared to zero.
    @since Sulfur-20171101
    @before 21.0-Scandium was unsound in many cases.
*)

val is_zero_comparable: term -> bool
(** [true] if the given term has a type for which a comparison to 0 exists
    (i.e. scalar C types, logic integers and reals).

    @since Sulfur-20171101
*)

val scalar_term_to_boolean: term -> term
(** Compare the given term with the constant 0 (of the appropriate type)
    to return the result of the comparison [e <> 0] as a boolean term.

    @raise Fatal error if the argument cannot be compared to 0
    @since 21.0-Scandium
*)

val scalar_term_to_predicate: term -> predicate
(** Compare the given term with the constant 0 (of the appropriate type)
    to return the result of the comparison [e <> 0].

    @raise Fatal error if the argument cannot be compared to 0
    @since Sulfur-20171101
*)

val lval_to_term_lval : lval -> term_lval
val host_to_term_lhost : lhost -> term_lhost
val offset_to_term_offset : offset -> term_offset

val constant_to_lconstant: constant -> logic_constant
val lconstant_to_constant: logic_constant-> constant

(** Parse the given string as a float or real logic constant.

    The parsed literal is always kept as it is in the resulting term.
    The returned term is either a real constant or
    real constant casted into a C-float type.

    Unsuffixed literals are considered as real numbers.
    Literals suffixed by [f|d|l] or [F|D|L] are considered
    as float constants of the associated kind. *)
val parse_float : ?loc:location -> string -> term

(** {2 Various Utilities} *)

(** [remove_term_offset o] returns [o] without its last offset and
    this last offset. *)
val remove_term_offset :
  term_offset -> term_offset * term_offset

(** true if \result is included in the lval. *)
val lval_contains_result : term_lhost -> bool

(** true if \result is included in the offset. *)
val loffset_contains_result : term_offset -> bool

(** true if \result is included in the term *)
val contains_result : term -> bool

(** returns the body of the given predicate.
    @raise Not_found if the logic_info is not the definition of a predicate. *)
val get_pred_body :
  logic_info -> predicate

(** true if the term is \result or an offset of \result. *)
val is_result : term -> bool

val lhost_c_type : term_lhost -> typ

(** [true] if the predicate is Ptrue.
    @since Nitrogen-20111001 *)
val is_trivially_true: predicate -> bool

(** [true] if the predicate is Pfalse
    @since Nitrogen-20111001 *)
val is_trivially_false: predicate -> bool

(** {2 Code annotations} *)

(** Does the annotation apply to the next statement (e.g. a statement
    contract). Also false for loop-related annotations.

    @since 21.0-Scandium
*)
val is_annot_next_stmt: code_annotation -> bool

(** {2 Global annotations} *)

(** add an attribute to a global annotation
    @since Phosphorus-20170501-beta1
*)
val add_attribute_glob_annot:
  attribute -> global_annotation -> global_annotation

(** {2 Contracts } *)

(** [true] if the behavior has only an assigns clause.
    @since 22.0-Titanium
*)
val behavior_has_only_assigns: behavior -> bool

(** [true] if the only non-empty fields of the contract are assigns clauses
    @since 22.0-Titanium
*)
val funspec_has_only_assigns: funspec -> bool

(** {2 Structural equality between annotations} *)

val is_same_list: ('a -> 'a -> bool) -> 'a list -> 'a list -> bool

val is_same_logic_label :
  logic_label -> logic_label -> bool

(**
   @since Nitrogen-20111001
*)
val is_same_pconstant: Logic_ptree.constant -> Logic_ptree.constant -> bool

val is_same_type : logic_type -> logic_type -> bool
val is_same_var : logic_var -> logic_var -> bool
val is_same_logic_signature :
  logic_info -> logic_info -> bool
val is_same_logic_profile :
  logic_info -> logic_info -> bool
val is_same_builtin_profile :
  builtin_logic_info -> builtin_logic_info -> bool
val is_same_logic_ctor_info :
  logic_ctor_info -> logic_ctor_info -> bool

val is_same_term : term -> term -> bool
val is_same_logic_info : logic_info -> logic_info -> bool
val is_same_logic_body : logic_body -> logic_body -> bool
val is_same_indcase :
  string * logic_label list * string list *
  predicate ->
  string * logic_label list * string list *
  predicate -> bool
val is_same_tlval : term_lval -> term_lval -> bool
val is_same_lhost : term_lhost -> term_lhost -> bool
val is_same_offset : term_offset -> term_offset -> bool
val is_same_predicate_node : predicate_node -> predicate_node -> bool
val is_same_predicate : predicate -> predicate -> bool
val is_same_identified_predicate :
  identified_predicate -> identified_predicate -> bool
val is_same_identified_term :
  identified_term -> identified_term -> bool
val is_same_deps : deps -> deps -> bool
val is_same_allocation :
  allocation -> allocation -> bool
val is_same_assigns :
  assigns -> assigns -> bool
val is_same_variant : variant -> variant -> bool
val is_same_post_cond :
  termination_kind * identified_predicate ->
  termination_kind * identified_predicate -> bool
val is_same_behavior : funbehavior -> funbehavior -> bool
val is_same_spec : funspec -> funspec -> bool
val is_same_logic_type_def :
  logic_type_def -> logic_type_def -> bool
val is_same_logic_type_info :
  logic_type_info -> logic_type_info -> bool
val is_same_loop_pragma : loop_pragma -> loop_pragma -> bool
val is_same_slice_pragma : slice_pragma -> slice_pragma -> bool
val is_same_impact_pragma : impact_pragma -> impact_pragma -> bool
val is_same_pragma : pragma -> pragma -> bool
val is_same_code_annotation : code_annotation -> code_annotation -> bool
val is_same_global_annotation : global_annotation -> global_annotation -> bool
val is_same_axiomatic :
  global_annotation list -> global_annotation list -> bool

(** @since Oxygen-20120901 *)
val is_same_model_info: model_info -> model_info -> bool

val is_same_lexpr: Logic_ptree.lexpr -> Logic_ptree.lexpr -> bool

(** hash function compatible with is_same_term *)
val hash_term: term -> int

(** comparison compatible with is_same_term *)
val compare_term: term -> term -> int

val hash_predicate: predicate -> int

val compare_predicate: predicate -> predicate -> int

(** {2 Merging contracts} *)

val get_behavior_names : spec -> string list

(** Concatenates two assigns if both are defined,
    returns WritesAny if one (or both) of them is WritesAny.
    @since Nitrogen-20111001 *)
val concat_assigns: assigns -> assigns -> assigns

(** merge assigns: take the one that is defined and select an arbitrary one
    if both are, emitting a warning unless both are syntactically the same. *)
val merge_assigns : assigns -> assigns -> assigns

(** Concatenates two allocation clauses if both are defined,
    returns FreeAllocAny if one (or both) of them is FreeAllocAny.
    @since Nitrogen-20111001 *)
val concat_allocation: allocation -> allocation -> allocation

(** merge allocation: take the one that is defined and select an arbitrary one
    if both are, emitting a warning unless both are syntactically the same.
    @since Oxygen-20120901 *)
val merge_allocation : allocation -> allocation -> allocation

val merge_behaviors :
  ?oldloc:location -> silent:bool -> funbehavior list -> funbehavior list -> funbehavior list

(** [merge_funspec ?oldloc oldspec newspec] merges [newspec] into [oldspec].
    If the funspec belongs to a kernel function, do not forget to call
    {!Kernel_function.set_spec} after merging.
*)
val merge_funspec :
  ?oldloc:location -> ?silent_about_merging_behav:bool ->
  funspec -> funspec -> unit

(** Reset the given funspec to empty.
    @since Nitrogen-20111001 *)
val clear_funspec: funspec -> unit

(** {2 Discriminating code_annotations} *)

(** Checks if a predicate kind can be used as an hypothesis or requirement.
    It is true for `Admit` and `Assert`, and false for `Check`. *)
val use_predicate : predicate_kind -> bool

(** Checks if a predicate kind shall be put under verification.
    It is true for `Assert` and `Check`, and false for `Admit`. *)
val verify_predicate : predicate_kind -> bool

(** Functions below allows to test a special kind of code_annotation.
    Use them in conjunction with {!Annotations.get_filter} to retrieve
    a particular kind of annotations associated to a statement. *)

val is_assert : code_annotation -> bool
val is_check : code_annotation -> bool
val is_admit : code_annotation -> bool
val is_contract : code_annotation -> bool
val is_stmt_invariant : code_annotation -> bool
val is_loop_invariant : code_annotation -> bool
val is_invariant : code_annotation -> bool
val is_variant : code_annotation -> bool
val is_allocation: code_annotation -> bool
val is_assigns : code_annotation -> bool
val is_pragma : code_annotation -> bool
val is_loop_pragma : code_annotation -> bool
val is_slice_pragma : code_annotation -> bool
val is_impact_pragma : code_annotation -> bool
val is_loop_annot : code_annotation -> bool

val is_trivial_annotation : code_annotation -> bool

val is_property_pragma : pragma -> bool
(** Should this pragma be proved by plugins *)

val extract_loop_pragma :
  code_annotation list -> loop_pragma list
val extract_contract :
  code_annotation list -> (string list * funspec) list

(** {2 Constant folding} *)

val constFoldTermToInt: ?machdep:bool -> term -> Integer.t option

(**
   A [cilVisitor] (by copy) that simplifies expressions of the type
   [const int x = v], where [v] is an integer and [x] is a global variable.
   Requires a mapping from [varinfo] to [init option]
   (e.g. based on [Globals.Vars.find]).

   @since Silicon-20161101
*)
class simplify_const_lval: (varinfo -> init option) -> Cil.cilVisitor

(** {2 Type-checking hackery} *)

(** give complete types to terms that refer to a variable whose type
    has been completed after its use in an annotation. Internal use only.
    @since Neon-20140301 *)
val complete_types: file -> unit

(** {2 Parsing hackery} *)
(** Values that control the various modes of the parser and lexer for logic.
    Use with care.
*)

val kw_c_mode : bool ref
val enter_kw_c_mode : unit -> unit
val exit_kw_c_mode : unit -> unit
val is_kw_c_mode : unit -> bool
val rt_type_mode : bool ref
val enter_rt_type_mode : unit -> unit
val exit_rt_type_mode : unit -> unit
val is_rt_type_mode : unit -> bool

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
