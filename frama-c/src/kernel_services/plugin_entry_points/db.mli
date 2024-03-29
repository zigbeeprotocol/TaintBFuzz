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

(** Database in which static plugins are registered.
    @plugin development guide *)

(**
   Modules providing general services:
   - {!Dynamic}: API for plug-ins linked dynamically
   - {!Journal}: journalisation
   - {!Log}: message outputs and printers
   - {!Plugin}: general services for plug-ins
   - {!Project} and associated files: {!Kind}, {!Datatype} and {!State_builder}.

   Other main kernel modules:
   - {!Ast}: the cil AST
   - {!Ast_info}: syntactic value directly computed from the Cil Ast
   - {!File}: Cil file initialization
   - {!Globals}: global variables, functions and annotations
   - {!Annotations}: annotations associated with a statement
   - {!Property_status}: status of annotations
   - {!Kernel_function}: C functions as seen by Frama-C
   - {!Stmts_graph}: the statement graph
   - {!Loop}: (natural) loops
   - {!Visitor}: frama-c visitors
   - {!Kernel}: general parameters of Frama-C (mostly set from the command
     line)
*)

open Cil_types
open Cil_datatype

(* ************************************************************************* *)
(** {2 Registering} *)
(* ************************************************************************* *)

(** How to journalize the given function.
    @since Beryllium-20090601-beta1 *)
type 'a how_to_journalize =
  | Journalize of string * 'a Type.t
  (** Journalize the value with the given name and type. *)
  | Journalization_not_required
  (** Journalization of this value is not required
      (usually because it has no effect on the Frama-C global state). *)
  | Journalization_must_not_happen of string
  (** Journalization of this value should not happen
      (usually because it is a low-level function: this function is always
      called from a journalized function).
      The string is the function name which is used for displaying suitable
      error message. *)

val register: 'a how_to_journalize -> 'a ref -> 'a -> unit
(** Plugins must register values with this function. *)

val register_compute:
  string ->
  State.t list ->
  (unit -> unit) ref -> (unit -> unit) -> State.t

val register_guarded_compute:
  string ->
  (unit -> bool) ->
  (unit -> unit) ref -> (unit -> unit) -> unit

(** Frama-C main interface.
    @since Lithium-20081201
    @plugin development guide *)
module Main: sig

  val extend : (unit -> unit) -> unit
  (** Register a function to be called by the Frama-C main entry point.
      @plugin development guide *)

  val play: (unit -> unit) ref
  (** Run all the Frama-C analyses. This function should be called only by
      toplevels.
      @since Beryllium-20090901 *)

  (**/**)
  val apply: unit -> unit
  (** Not for casual user. *)
  (**/**)

end

module Toplevel: sig

  val run: ((unit -> unit) -> unit) ref
  (** Run a Frama-C toplevel playing the game given in argument (in
      particular, applying the argument runs the analyses).
      @since Beryllium-20090901 *)

end

(* ************************************************************************* *)
(** {2 Values} *)
(* ************************************************************************* *)

(** The Value analysis itself.
    @see <../value/index.html> internal documentation. *)
module Value : sig

  type state = Cvalue.Model.t
  (** Internal state of the value analysis. *)

  type t = Cvalue.V.t
  (** Internal representation of a value. *)

  val emitter: Emitter.t ref
  (** Emitter used by Value to emit statuses *)

  val proxy: State_builder.Proxy.t

  val self : State.t
  (** Internal state of the value analysis from projects viewpoint.
      @plugin development guide *)

  val mark_as_computed: unit -> unit
  (** Indicate that the value analysis has been done already. *)

  val compute : (unit -> unit) ref
  (** Compute the value analysis using the entry point of the current
      project. You may set it with {!Globals.set_entry_point}.
      @raise Globals.No_such_entry_point if the entry point is incorrect
      @raise Db.Value.Incorrect_number_of_arguments if some arguments are
      specified for the entry point using {!Db.Value.fun_set_args}, and
      an incorrect number of them is given.
      @plugin development guide *)

  val is_computed: unit -> bool
  (** Return [true] iff the value analysis has been done.
      @plugin development guide *)

  module Table_By_Callstack:
    State_builder.Hashtbl with type key = stmt
                           and type data = state Value_types.Callstack.Hashtbl.t
  (** Table containing the results of the value analysis, ie.
      the state before the evaluation of each reachable statement. *)

  module AfterTable_By_Callstack:
    State_builder.Hashtbl with type key = stmt
                           and type data = state Value_types.Callstack.Hashtbl.t
  (** Table containing the state of the value analysis after the evaluation
      of each reachable and evaluable statement. Filled only if
      [Value_parameters.ResultsAfter] is set. *)

  val ignored_recursive_call: kernel_function -> bool
  (** This functions returns true if the value analysis found and ignored
      a recursive call to this function during the analysis. *)

  val condition_truth_value: stmt -> bool * bool
  (** Provided [stmt] is an 'if' construct, [fst (condition_truth_value stmt)]
      (resp. snd) is true if and only if the condition of the 'if' has been
      evaluated to true (resp. false) at least once during the analysis. *)

  (** {3 Parameterization} *)

  val use_spec_instead_of_definition: (kernel_function -> bool) ref
  (** To be called by derived analyses to determine if they must use
      the body of the function (if available), or only its spec. Used for
      value builtins, and option -val-use-spec. *)


  (** {4 Arguments of the main function} *)

  (** The functions below are related to the arguments that are passed to the
      function that is analysed by the value analysis. Specific arguments
      are set by [fun_set_args]. Arguments reset to default values when
      [fun_use_default_args] is called, when the ast is changed, or
      if the options [-libentry] or [-main] are changed. *)

  (** Specify the arguments to use. This function is not journalized, and
      will generate an error when the journal is replayed *)
  val fun_set_args : t list -> unit

  val fun_use_default_args : unit -> unit

  (** For this function, the result [None] means that
      default values are used for the arguments. *)
  val fun_get_args : unit -> t list option

  exception Incorrect_number_of_arguments
  (** Raised by [Db.Compute] when the arguments set by [fun_set_args]
      are not coherent with the prototype of the function (if there are
      too few or too many of them) *)


  (** {4 Initial state of the analysis} *)

  (** The functions below are related to the value of the global variables
      when the value analysis is started. If [globals_set_initial_state] has not
      been called, the given state is used. A default state (which depends on
      the option [-libentry]) is used when [globals_use_default_initial_state]
      is called, or when the ast changes. *)

  (** Specify the initial state to use. This function is not journalized,
      and will generate an error when the journal is replayed *)
  val globals_set_initial_state : state -> unit

  val globals_use_default_initial_state : unit -> unit

  (** Initial state used by the analysis *)
  val globals_state : unit -> state


  (** @return [true] if the initial state for globals used by the value
      analysis has been supplied by the user (through
      [globals_set_initial_state]), or [false] if it is automatically
      computed by the value analysis *)
  val globals_use_supplied_state : unit -> bool


  (** {3 Getters} *)
  (** State of the analysis at various points *)

  val get_initial_state : kernel_function -> state
  val get_initial_state_callstack :
    kernel_function -> state Value_types.Callstack.Hashtbl.t option
  val get_state : ?after:bool -> kinstr -> state
  (** [after] is false by default. *)

  val get_stmt_state_callstack:
    after:bool -> stmt -> state Value_types.Callstack.Hashtbl.t option

  val get_stmt_state : ?after:bool -> stmt -> state
  (** [after] is false by default.
      @plugin development guide *)

  val fold_stmt_state_callstack :
    (state -> 'a -> 'a) -> 'a -> after:bool -> stmt -> 'a

  val fold_state_callstack :
    (state -> 'a -> 'a) -> 'a -> after:bool -> kinstr -> 'a

  val find : state -> Locations.location ->  t

  (** {3 Evaluations} *)

  val eval_lval :
    (?with_alarms:CilE.warn_mode ->
     Locations.Zone.t option ->
     state ->
     lval ->
     Locations.Zone.t option * t) ref

  val eval_expr :
    (?with_alarms:CilE.warn_mode -> state -> exp -> t) ref

  val eval_expr_with_state :
    (?with_alarms:CilE.warn_mode -> state -> exp -> state * t) ref

  val reduce_by_cond:
    (state -> exp -> bool -> state) ref

  val find_lv_plus :
    (Cvalue.Model.t -> Cil_types.exp ->
     (Cil_types.lval * Ival.t) list) ref
  (** returns the list of all decompositions of [expr] into the sum an lvalue
      and an interval. *)

  (** {3 Values and kernel functions} *)

  val expr_to_kernel_function :
    (kinstr
     -> ?with_alarms:CilE.warn_mode
     -> deps:Locations.Zone.t option
     -> exp
     -> Locations.Zone.t * Kernel_function.Hptset.t) ref

  val expr_to_kernel_function_state :
    (state
     -> deps:Locations.Zone.t option
     -> exp
     -> Locations.Zone.t * Kernel_function.Hptset.t) ref

  exception Not_a_call
  val call_to_kernel_function : stmt -> Kernel_function.Hptset.t
  (** Return the functions that can be called from this call.
      @raise Not_a_call if the statement is not a call. *)

  val valid_behaviors: (kernel_function -> state -> funbehavior list) ref

  val add_formals_to_state: (state -> kernel_function -> exp list -> state) ref
  (** [add_formals_to_state state kf exps] evaluates [exps] in [state]
      and binds them to the formal arguments of [kf] in the resulting
      state *)

  (** {3 Reachability} *)

  val is_accessible : kinstr -> bool
  val is_reachable : state -> bool
  (** @plugin development guide *)

  val is_reachable_stmt : stmt -> bool

  (** {3 About kernel functions} *)

  exception Void_Function
  val find_return_loc : kernel_function -> Locations.location
  (** Return the location of the returned lvalue of the given function.
      @raise Void_Function if the function does not return any value. *)

  val is_called: (kernel_function -> bool) ref

  val callers: (kernel_function -> (kernel_function*stmt list) list) ref
  (** @return the list of callers with their call sites. Each function is
      present only once in the list. *)

  (** {3 State before a kinstr} *)

  val access : (kinstr -> lval ->  t) ref
  val access_expr : (kinstr -> exp ->  t) ref
  val access_location : (kinstr -> Locations.location ->  t) ref


  (** {3 Locations of left values} *)

  val lval_to_loc :
    (kinstr -> ?with_alarms:CilE.warn_mode -> lval -> Locations.location) ref

  val lval_to_loc_with_deps :
    (kinstr
     -> ?with_alarms:CilE.warn_mode
     -> deps:Locations.Zone.t
     -> lval
     -> Locations.Zone.t * Locations.location) ref

  val lval_to_loc_with_deps_state :
    (state
     -> deps:Locations.Zone.t
     -> lval
     -> Locations.Zone.t * Locations.location) ref

  val lval_to_loc_state :
    (state -> lval -> Locations.location) ref

  val lval_to_offsetmap :
    ( kinstr -> ?with_alarms:CilE.warn_mode -> lval ->
      Cvalue.V_Offsetmap.t option) ref

  val lval_to_offsetmap_state :
    (state -> lval -> Cvalue.V_Offsetmap.t option) ref
  (** @since Carbon-20110201 *)

  val lval_to_zone :
    (kinstr -> ?with_alarms:CilE.warn_mode -> lval -> Locations.Zone.t) ref

  val lval_to_zone_state :
    (state -> lval -> Locations.Zone.t) ref
  (** Does not emit alarms. *)

  val lval_to_zone_with_deps_state:
    (state -> for_writing:bool -> deps:Locations.Zone.t option -> lval ->
     Locations.Zone.t * Locations.Zone.t * bool) ref
  (** [lval_to_zone_with_deps_state state ~for_writing ~deps lv] computes
      [res_deps, zone_lv, exact], where [res_deps] are the memory zones needed
      to evaluate [lv] in [state] joined  with [deps]. [zone_lv] contains the
      valid memory zones that correspond to the location that [lv] evaluates
      to in [state]. If [for_writing] is true, [zone_lv] is restricted to
      memory zones that are writable. [exact] indicates that [lv] evaluates
      to a valid location of cardinal at most one. *)

  val lval_to_precise_loc_state:
    (?with_alarms:CilE.warn_mode -> state -> lval ->
     state * Precise_locs.precise_location * typ) ref

  val lval_to_precise_loc_with_deps_state:
    (state -> deps:Locations.Zone.t option -> lval ->
     Locations.Zone.t * Precise_locs.precise_location) ref


  (** Evaluation of the [\from] clause of an [assigns] clause.*)
  val assigns_inputs_to_zone :
    (state -> assigns -> Locations.Zone.t) ref

  (** Evaluation of the left part of [assigns] clause (without [\from]).*)
  val assigns_outputs_to_zone :
    (state -> result:varinfo option -> assigns -> Locations.Zone.t) ref

  (** Evaluation of the left part of [assigns] clause (without [\from]). Each
      assigns term results in one location. *)
  val assigns_outputs_to_locations :
    (state -> result:varinfo option -> assigns -> Locations.location list) ref

  (** For internal use only. Evaluate the [assigns] clause of the
      given function in the given prestate, compare it with the
      computed froms, return warning and set statuses. *)
  val verify_assigns_froms :
    (Kernel_function.t -> pre:state -> Function_Froms.t -> unit) ref


  (** {3 Evaluation of logic terms and predicates} *)
  module Logic : sig
    (** The APIs of this module are not stabilized yet, and are subject
        to change between Frama-C versions. *)

    val eval_predicate:
      (pre:state -> here:state -> predicate ->
       Property_status.emitted_status) ref
      (** Evaluate the given predicate in the given states for the Pre
          and Here ACSL labels.
          @since Neon-20140301 *)
  end


  (** {3 Callbacks} *)

  type callstack = Value_types.callstack

  (** Actions to perform at end of each function analysis. Not compatible with
      option [-memexec-all] *)

  module Record_Value_Callbacks:
    Hook.Iter_hook with type param = callstack * (state Stmt.Hashtbl.t) Lazy.t

  module Record_Value_Superposition_Callbacks:
    Hook.Iter_hook with type param = callstack * (state list Stmt.Hashtbl.t) Lazy.t

  module Record_Value_After_Callbacks:
    Hook.Iter_hook with type param = callstack * (state Stmt.Hashtbl.t) Lazy.t

  (**/**)
  (* Temporary API, do not use *)
  module Record_Value_Callbacks_New: Hook.Iter_hook
    with type param =
           callstack *
           ((state Stmt.Hashtbl.t) Lazy.t  (* before states *) *
            (state Stmt.Hashtbl.t) Lazy.t) (* after states *)
             Value_types.callback_result
  (**/**)

  val no_results: (fundec -> bool) ref
  (** Returns [true] if the user has requested that no results should
      be recorded for this function. If possible, hooks registered
      on [Record_Value_Callbacks] and [Record_Value_Callbacks_New]
      should not force their lazy argument *)

  (** Actions to perform at each treatment of a "call"
      statement. [state] is the state before the call.
      @deprecated Use Call_Type_Value_Callbacks instead. *)
  module Call_Value_Callbacks:
    Hook.Iter_hook with type param = state * callstack

  (** Actions to perform at each treatment of a "call"
      statement. [state] is the state before the call.
      @since Aluminium-20160501  *)
  module Call_Type_Value_Callbacks:
    Hook.Iter_hook with type param =
                          [`Builtin of Value_types.call_froms | `Spec of funspec | `Def | `Memexec]
                          * state * callstack


  (** Actions to perform whenever a statement is handled. *)
  module Compute_Statement_Callbacks:
    Hook.Iter_hook with type param = stmt * callstack * state list

  (* -remove-redundant-alarms feature, applied at the end of an Eva analysis,
     fulfilled by the Scope plugin that also depends on Eva. We thus use a
     reference here to avoid a cyclic dependency. *)
  val rm_asserts: (unit -> unit) ref


  (** {3 Pretty printing} *)

  val pretty : Format.formatter -> t -> unit
  val pretty_state : Format.formatter -> state -> unit


  val display : (Format.formatter -> kernel_function -> unit) ref

  (**/**)
  (** {3 Internal use only} *)

  val noassert_get_state : ?after:bool -> kinstr -> state
  (** To be used during the value analysis itself (instead of
      {!get_state}). [after] is false by default. *)

  val recursive_call_occurred: kernel_function -> unit

  val merge_conditions: int Cil_datatype.Stmt.Hashtbl.t -> unit
  val mask_then: int
  val mask_else: int

  val initial_state_only_globals : (unit -> state) ref

  val update_callstack_table: after:bool -> stmt -> callstack -> state -> unit
  (* Merge a new state in the table indexed by callstacks. *)


  val memoize : (kernel_function -> unit) ref
  (*  val compute_call :
      (kernel_function -> call_kinstr:kinstr -> state ->  (exp*t) list
         -> Cvalue.V_Offsetmap.t option (** returned value of [kernel_function] *) * state) ref
  *)
  val merge_initial_state : callstack -> state -> unit
  (** Store an additional possible initial state for the given callstack as
      well as its values for actuals. *)

  val initial_state_changed: (unit -> unit) ref
end

(** Functional dependencies between function inputs and function outputs.
    @see <../from/index.html> internal documentation. *)
module From : sig

  (** exception raised by [find_deps_no_transitivity_*] if the given expression
      is not an lvalue.
      @since Aluminium-20160501
  *)
  exception Not_lval

  val compute_all : (unit -> unit) ref
  val compute_all_calldeps : (unit -> unit) ref

  val compute : (kernel_function -> unit) ref

  val is_computed: (kernel_function -> bool) ref
  (** Check whether the from analysis has been performed for the given
      function.
      @return true iff the analysis has been performed *)

  val get : (kernel_function -> Function_Froms.t) ref
  val access : (Locations.Zone.t -> Function_Froms.Memory.t
                -> Locations.Zone.t) ref

  val find_deps_no_transitivity : (stmt -> exp -> Locations.Zone.t) ref

  val find_deps_no_transitivity_state :
    (Value.state -> exp -> Locations.Zone.t) ref

  (** @raise Not_lval if the given expression is not a C lvalue. *)
  val find_deps_term_no_transitivity_state :
    (Value.state -> term -> Value_types.logic_dependencies) ref

  val self: State.t ref

  (** {3 Pretty printing} *)

  val pretty : (Format.formatter -> kernel_function -> unit) ref
  val display : (Format.formatter -> unit) ref

  (** {3 Callback} *)

  module Record_From_Callbacks:
    Hook.Iter_hook with type param =
                          Kernel_function.t Stack.t *
                          Function_Froms.Memory.t Stmt.Hashtbl.t *
                          (Kernel_function.t * Function_Froms.Memory.t) list
                            Stmt.Hashtbl.t

  (** {3 Access to callwise-stored data} *)

  module Callwise : sig
    val iter : ((kinstr -> Function_Froms.t -> unit) -> unit) ref
    val find : (kinstr -> Function_Froms.t) ref
  end
end

(* ************************************************************************* *)
(** {2 Properties} *)
(* ************************************************************************* *)

(** Dealing with logical properties.
    @plugin development guide *)
module Properties : sig

  (** Interpretation of logic terms. *)
  module Interp : sig

    (** {3 Parsing logic terms and annotations} *)

    (** For the three functions below, [env] can be used to specify which
        logic labels are parsed. By default, only [Here] is accepted. All
        the C labels inside the function are also  accepted, regardless of
        [env]. [loc] is used as the source for the beginning of the string.
        All three functions may raise {!Logic_interp.Error} or
        {!Parsing.Parse_error}. *)

    val term_lval :
      (kernel_function -> ?loc:location -> ?env:Logic_typing.Lenv.t -> string ->
       Cil_types.term_lval) ref
    val term :
      (kernel_function -> ?loc:location -> ?env:Logic_typing.Lenv.t -> string ->
       Cil_types.term) ref
    val predicate :
      (kernel_function -> ?loc:location -> ?env:Logic_typing.Lenv.t -> string ->
       Cil_types.predicate) ref

    val code_annot : (kernel_function -> stmt -> string -> code_annotation) ref


    (** {3 From logic terms to C terms} *)

    (** Exception raised by the functions below when their given argument
        cannot be interpreted in the C world.
        @since Aluminium-20160501
    *)
    exception No_conversion

    val term_lval_to_lval:
      (result: Cil_types.varinfo option -> term_lval -> Cil_types.lval) ref
    (** @raise No_conversion if the argument is not a left value. *)

    val term_to_lval:
      (result: Cil_types.varinfo option -> term -> Cil_types.lval) ref
    (** @raise No_conversion if the argument is not a left value. *)

    val term_to_exp:
      (result: Cil_types.varinfo option -> term -> Cil_types.exp) ref
    (** @raise No_conversion if the argument is not a valid expression. *)

    val loc_to_exp:
      (result: Cil_types.varinfo option -> term -> Cil_types.exp list) ref
    (** @return a list of C expressions.
        @raise No_conversion if the argument is not a valid set of
        expressions. *)

    val loc_to_lval:
      (result: Cil_types.varinfo option -> term -> Cil_types.lval list) ref
    (** @return a list of C locations.
        @raise No_conversion if the argument is not a valid set of
        left values. *)

    val term_offset_to_offset:
      (result: Cil_types.varinfo option -> term_offset -> offset) ref
    (** @raise No_conversion if the argument is not a valid offset. *)

    val loc_to_offset:
      (result: Cil_types.varinfo option -> term -> Cil_types.offset list) ref
    (** @return a list of C offset provided the term denotes locations who
        have all the same base address.
        @raise No_conversion if the given term does not match the precondition *)


    (** {3 From logic terms to Locations.location} *)

    val loc_to_loc:
      (result: Cil_types.varinfo option -> Value.state -> term ->
       Locations.location) ref
    (** @raise No_conversion if the translation fails. *)

    val loc_to_loc_under_over:
      (result: Cil_types.varinfo option -> Value.state -> term ->
       Locations.location * Locations.location * Locations.Zone.t) ref
    (** Same as {!loc_to_loc}, except that we return simultaneously an
        under-approximation of the term (first location), and an
        over-approximation (second location). The under-approximation
        is particularly useful when evaluating Tsets. The zone returned is an
        over-approximation of locations that have been read during evaluation.
        Warning: This API is not stabilized, and may change in
        the future.
        @raise No_conversion if the translation fails.
    *)

    (** {3 From logic terms to Zone.t} *)

    module To_zone : sig
      type t_ctx =
        {state_opt:bool option;
         ki_opt:(stmt * bool) option;
         kf:Kernel_function.t}

      val mk_ctx_func_contrat:
        (kernel_function -> state_opt:bool option -> t_ctx) ref
      (** To build an interpretation context relative to function
          contracts. *)

      val mk_ctx_stmt_contrat:
        (kernel_function -> stmt -> state_opt:bool option -> t_ctx) ref
      (** To build an interpretation context relative to statement
          contracts. *)

      val mk_ctx_stmt_annot:
        (kernel_function -> stmt -> t_ctx) ref
      (** To build an interpretation context relative to statement
          annotations. *)

      type t = {before:bool ; ki:stmt ; zone:Locations.Zone.t}
      type t_zone_info = (t list) option
      (** list of zones at some program points.
       *   None means that the computation has failed. *)

      type t_decl = {var: Varinfo.Set.t ; (* related to vars of the annot *)
                     lbl: Logic_label.Set.t} (* related to labels of the annot *)
      type t_pragmas =
        {ctrl: Stmt.Set.t ; (* related to //@ slice pragma ctrl/expr *)
         stmt: Stmt.Set.t}  (* related to statement assign and
                               //@ slice pragma stmt *)

      val from_term: (term -> t_ctx -> t_zone_info * t_decl) ref
      (** Entry point to get zones needed to evaluate the [term] relative to
          the [ctx] of interpretation. *)

      val from_terms: (term list -> t_ctx -> t_zone_info * t_decl) ref
      (** Entry point to get zones needed to evaluate the list of [terms]
          relative to the [ctx] of interpretation. *)

      val from_pred: (predicate -> t_ctx -> t_zone_info * t_decl) ref
      (** Entry point to get zones needed to evaluate the [predicate]
          relative to the [ctx] of interpretation. *)

      val from_preds: (predicate list -> t_ctx -> t_zone_info * t_decl) ref
      (** Entry point to get zones needed to evaluate the list of
          [predicates] relative to the [ctx] of interpretation. *)

      val from_zone: (identified_term -> t_ctx -> t_zone_info * t_decl) ref
      (** Entry point to get zones needed to evaluate the [zone] relative to
          the [ctx] of interpretation. *)

      val from_stmt_annot:
        (code_annotation -> stmt * kernel_function
         -> (t_zone_info * t_decl) * t_pragmas) ref
      (** Entry point to get zones needed to evaluate an annotation on the
          given stmt. *)

      val from_stmt_annots:
        ((code_annotation -> bool) option ->
         stmt * kernel_function -> (t_zone_info * t_decl) * t_pragmas) ref
      (** Entry point to get zones needed to evaluate annotations of this
          [stmt]. *)

      val from_func_annots:
        (((stmt -> unit) -> kernel_function -> unit) ->
         (code_annotation -> bool) option ->
         kernel_function -> (t_zone_info * t_decl) * t_pragmas) ref
      (** Entry point to get zones
          needed to evaluate annotations of this [kf]. *)

      val code_annot_filter:
        (code_annotation ->
         threat:bool -> user_assert:bool -> slicing_pragma:bool ->
         loop_inv:bool -> loop_var:bool -> others:bool -> bool) ref
        (** To quickly build an annotation filter *)

    end

    (** Does the interpretation of the predicate rely on the interpretation
        of the term result?
        @since Carbon-20110201 *)
    val to_result_from_pred:
      (predicate -> bool) ref


  end

end

(* ************************************************************************* *)
(** {2 Plugins} *)
(* ************************************************************************* *)

(** Declarations common to the various postdominators-computing modules *)
module PostdominatorsTypes: sig

  exception Top
  (** Used for postdominators-related functions, when the
      postdominators of a statement cannot be computed. It means that
      there is no path from this statement to the function return. *)

  module type Sig = sig
    val compute: (kernel_function -> unit) ref

    val stmt_postdominators:
      (kernel_function -> stmt -> Stmt.Hptset.t) ref
    (** @raise Top (see above) *)

    val is_postdominator:
      (kernel_function -> opening:stmt -> closing:stmt -> bool) ref

    val display: (unit -> unit) ref

    val print_dot : (string -> kernel_function -> unit) ref
    (** Print a representation of the postdominators in a dot file
        whose name is [basename.function_name.dot]. *)
  end
end

(** Syntactic postdominators plugin.
    @see <../postdominators/index.html> internal documentation. *)
module Postdominators: PostdominatorsTypes.Sig

(** Postdominators using value analysis results.
    @see <../postdominators/index.html> internal documentation. *)
module PostdominatorsValue: PostdominatorsTypes.Sig

(** Runtime Error Annotation Generation plugin.
    @see <../rte/index.html> internal documentation. *)
module RteGen : sig
  (** Same result as having [-rte] on the command line*)
  val compute : (unit -> unit) ref

  (** Generates RTE for a single function. Uses the status of the various
      RTE options do decide which kinds of annotations must be generated.
  *)
  val annotate_kf : (kernel_function -> unit) ref

  (** Generates all possible RTE for a given function. *)
  val do_all_rte : (kernel_function -> unit) ref

  (** Generates all possible RTE except pre-conditions for a given function. *)
  val do_rte : (kernel_function -> unit) ref

  val self: State.t ref
  type status_accessor =
    string (* name *)
    * (kernel_function -> bool -> unit) (* for each kf and each kind of
                                           annotation, set/unset the fact
                                           that there has been generated *)
    * (kernel_function -> bool) (* is this kind of annotation generated in
                                   kf? *)
  val get_all_status : (unit -> status_accessor list) ref
  val get_divMod_status : (unit -> status_accessor) ref
  val get_initialized_status: (unit -> status_accessor) ref
  val get_memAccess_status : (unit -> status_accessor) ref
  val get_pointerCall_status: (unit -> status_accessor) ref
  val get_signedOv_status : (unit -> status_accessor) ref
  val get_signed_downCast_status : (unit -> status_accessor) ref
  val get_unsignedOv_status : (unit -> status_accessor) ref
  val get_unsignedDownCast_status : (unit -> status_accessor) ref
  val get_pointer_downcast_status : (unit -> status_accessor) ref
  val get_float_to_int_status : (unit -> status_accessor) ref
  val get_finite_float_status : (unit -> status_accessor) ref
  val get_pointer_value_status : (unit -> status_accessor) ref
  val get_bool_value_status : (unit -> status_accessor) ref
end


(** Security analysis.
    @see <../security/index.html> internal documentation. *)
module Security : sig

  val run_whole_analysis: (unit -> unit) ref
  (** Run all the security analysis. *)

  val run_ai_analysis: (unit -> unit) ref
  (** Only run the analysis by abstract interpretation. *)

  val run_slicing_analysis: (unit -> Project.t) ref
  (** Only run the security slicing pre-analysis. *)

  val self: State.t ref

end

(** Program Dependence Graph.
    @see <../pdg/index.html> PDG internal documentation. *)
module Pdg : sig

  exception Bottom
  (** Raised by most function when the PDG is Bottom because we can hardly do
      nothing with it. It happens when the function is unreachable because we
      have no information about it. *)

  exception Top
  (** Raised by most function when the PDG is Top because we can hardly do
      nothing with it. It happens when we didn't manage to compute it, for
      instance for a variadic function. *)

  type t = PdgTypes.Pdg.t
  (** PDG type *)

  type t_nodes_and_undef =
    ((PdgTypes.Node.t * Locations.Zone.t option) list * Locations.Zone.t option)
  (** type for the return value of many [find_xxx] functions when the
      answer can be a list of [(node, z_part)] and an [undef zone].
      For each node, [z_part] can specify which part of the node
      is used in terms of zone ([None] means all).
  *)

  val self : State.t ref

  (** {3 Getters} *)

  val get : (kernel_function -> t) ref
  (** Get the PDG of a function. Build it if it doesn't exist yet. *)

  val node_key : (PdgTypes.Node.t -> PdgIndex.Key.t) ref

  val from_same_fun : t -> t -> bool

  (** {3 Finding PDG nodes} *)

  val find_decl_var_node : (t -> Cil_types.varinfo -> PdgTypes.Node.t) ref
  (** Get the node corresponding the declaration of a local variable or a
      formal parameter.
      @raise Not_found if the variable is not declared in this function.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val find_ret_output_node : (t -> PdgTypes.Node.t) ref
  (** Get the node corresponding return stmt.
      @raise Not_found if the output state in unreachable
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val find_output_nodes :
    (t -> PdgIndex.Signature.out_key -> t_nodes_and_undef) ref
  (** Get the nodes corresponding to a call output key in the called pdg.
      @raise Not_found if the output state in unreachable
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val find_input_node : (t -> int -> PdgTypes.Node.t) ref
  (** Get the node corresponding to a given input (parameter).
      @raise Not_found if the number is not an input number.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val find_all_inputs_nodes : (t -> PdgTypes.Node.t list) ref
  (** Get the nodes corresponding to all inputs.
      {!node_key} can be used to know their numbers.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val find_stmt_node : (t -> Cil_types.stmt -> PdgTypes.Node.t) ref
  (** Get the node corresponding to the statement.
      It shouldn't be a call statement.
      See also {!find_simple_stmt_nodes} or {!find_call_stmts}.
      @raise Not_found if the given statement is unreachable.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top.
      @raise PdgIndex.CallStatement if the given stmt is a function
      call. *)


  val find_simple_stmt_nodes : (t -> Cil_types.stmt -> PdgTypes.Node.t list) ref
  (** Get the nodes corresponding to the statement.
      It is usually composed of only one node (see {!find_stmt_node}),
      except for call statement.
      Be careful that for block statements, it only returns a node
      corresponding to the elementary stmt
                         (see {!find_stmt_and_blocks_nodes} for more)
      @raise Not_found if the given statement is unreachable.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val find_label_node : (t -> Cil_types.stmt -> Cil_types.label -> PdgTypes.Node.t) ref
  (** Get the node corresponding to the label.
      @raise Not_found if the given label is not in the PDG.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val find_stmt_and_blocks_nodes : (t -> Cil_types.stmt -> PdgTypes.Node.t list) ref
  (** Get the nodes corresponding to the statement like
   * {!find_simple_stmt_nodes} but also add the nodes of the enclosed
   * statements if [stmt] contains blocks.
      @raise Not_found if the given statement is unreachable.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val find_top_input_node : (t -> PdgTypes.Node.t) ref
  (** @raise Not_found if there is no top input in the PDG.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val find_entry_point_node : (t -> PdgTypes.Node.t) ref
  (** Find the node that represent the entry point of the function, i.e. the
      higher level block.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val find_location_nodes_at_stmt :
    (t -> Cil_types.stmt -> before:bool -> Locations.Zone.t
     -> t_nodes_and_undef) ref
  (** Find the nodes that define the value of the location at the given
      program point. Also return a zone that might be undefined at that
      point.
      @raise Not_found if the given statement is unreachable.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val find_location_nodes_at_end :
    (t -> Locations.Zone.t -> t_nodes_and_undef) ref
  (** Same than {!find_location_nodes_at_stmt} for the program point located
      at the end of the function.
      @raise Not_found if the output state is unreachable.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val find_location_nodes_at_begin :
    (t -> Locations.Zone.t -> t_nodes_and_undef) ref
  (** Same than {!find_location_nodes_at_stmt} for the program point located
      at the beginning of the function.
      Notice that it can only find formal argument nodes.
      The remaining zone (implicit input) is returned as undef.
      @raise Not_found if the output state is unreachable.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val find_call_stmts:
    (kernel_function -> caller:kernel_function -> Cil_types.stmt list) ref
  (** Find the call statements to the function (can maybe be somewhere
      else).
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val find_call_ctrl_node : (t ->  Cil_types.stmt -> PdgTypes.Node.t) ref
  (** @raise Not_found if the call is unreachable.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val find_call_input_node : (t ->  Cil_types.stmt -> int -> PdgTypes.Node.t) ref
  (** @raise Not_found if the call is unreachable or has no such input.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val find_call_output_node : (t ->  Cil_types.stmt -> PdgTypes.Node.t) ref
  (** @raise Not_found if the call is unreachable or has no output node.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val find_code_annot_nodes :
    (t -> Cil_types.stmt -> Cil_types.code_annotation ->
     PdgTypes.Node.t list * PdgTypes.Node.t list * (t_nodes_and_undef option)) ref
  (** The result is composed of three parts :
      - the first part of the result are the control dependencies nodes
        of the annotation,
      - the second part is the list of declaration nodes of the variables
        used in the annotation;
      - the third part is similar to [find_location_nodes_at_stmt] result
        but  for all the locations needed by the annotation.
        When the third part  is globally [None],
        it means that we were not able to compute this information.
        @raise Not_found if the statement is unreachable.
        @raise Bottom if given PDG is bottom.
        @raise Top if the given pdg is top. *)

  val find_fun_precond_nodes :
    (t -> Cil_types.predicate -> PdgTypes.Node.t list * (t_nodes_and_undef option)) ref
  (** Similar to [find_code_annot_nodes] (no control dependencies nodes) *)

  val find_fun_postcond_nodes :
    (t -> Cil_types.predicate -> PdgTypes.Node.t list * (t_nodes_and_undef option)) ref
  (** Similar to [find_fun_precond_nodes] *)

  val find_fun_variant_nodes :
    (t -> Cil_types.term -> (PdgTypes.Node.t list * t_nodes_and_undef option)) ref
  (** Similar to [find_fun_precond_nodes] *)

  (** {3 Propagation}
      See also [Pdg.mli] for more function that cannot be here because
        they use polymorphic types.
   **)

  val find_call_out_nodes_to_select :
    (t -> PdgTypes.NodeSet.t -> t ->  Cil_types.stmt -> PdgTypes.Node.t list) ref
  (** [find_call_out_nodes_to_select pdg_called called_selected_nodes
      pdg_caller call_stmt]
      @return the call outputs nodes [out] such that
      [find_output_nodes pdg_called out_key]
      intersects [called_selected_nodes]. *)

  val find_in_nodes_to_select_for_this_call :
    (t -> PdgTypes.NodeSet.t -> Cil_types.stmt -> t -> PdgTypes.Node.t list) ref
  (** [find_in_nodes_to_select_for_this_call
      pdg_caller caller_selected_nodes call_stmt pdg_called]
      @return the called input nodes such that the corresponding nodes
      in the caller intersect [caller_selected_nodes]
      @raise Not_found if the statement is unreachable.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  (** {3 Dependencies} *)

  val direct_dpds : (t -> PdgTypes.Node.t -> PdgTypes.Node.t list) ref
  (** Get the nodes to which the given node directly depend on.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val direct_ctrl_dpds : (t -> PdgTypes.Node.t -> PdgTypes.Node.t list) ref
  (** Similar to {!direct_dpds}, but for control dependencies only.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val direct_data_dpds : (t -> PdgTypes.Node.t -> PdgTypes.Node.t list) ref
  (** Similar to {!direct_dpds}, but for data dependencies only.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val direct_addr_dpds : (t -> PdgTypes.Node.t -> PdgTypes.Node.t list) ref
  (** Similar to {!direct_dpds}, but for address dependencies only.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val all_dpds : (t -> PdgTypes.Node.t list -> PdgTypes.Node.t list) ref
  (** Transitive closure of {!direct_dpds} for all the given nodes.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val all_data_dpds : (t -> PdgTypes.Node.t list -> PdgTypes.Node.t list) ref
  (** Gives the data dependencies of the given nodes, and recursively, all
      the dependencies of those nodes (regardless to their kind).
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val all_ctrl_dpds : (t -> PdgTypes.Node.t list -> PdgTypes.Node.t list) ref
  (** Similar to {!all_data_dpds} for control dependencies.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val all_addr_dpds : (t -> PdgTypes.Node.t list -> PdgTypes.Node.t list) ref
  (** Similar to {!all_data_dpds} for address dependencies.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val direct_uses : (t -> PdgTypes.Node.t -> PdgTypes.Node.t list) ref
  (** build a list of all the nodes that have direct dependencies on the
      given node.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val direct_ctrl_uses : (t -> PdgTypes.Node.t -> PdgTypes.Node.t list) ref
  (** Similar to {!direct_uses}, but for control dependencies only.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val direct_data_uses : (t -> PdgTypes.Node.t -> PdgTypes.Node.t list) ref
  (** Similar to {!direct_uses}, but for data dependencies only.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val direct_addr_uses : (t -> PdgTypes.Node.t -> PdgTypes.Node.t list) ref
  (** Similar to {!direct_uses}, but for address dependencies only.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val all_uses : (t -> PdgTypes.Node.t list -> PdgTypes.Node.t list) ref
  (** build a list of all the nodes that have dependencies (even indirect) on
      the given nodes.
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val custom_related_nodes :
    ((PdgTypes.Node.t -> PdgTypes.Node.t list) -> PdgTypes.Node.t list -> PdgTypes.Node.t list) ref
  (** [custom_related_nodes get_dpds node_list] build a list, starting from
      the node in [node_list], and recursively add the nodes given by the
      function [get_dpds].  For this function to work well, it is important
      that [get_dpds n] returns a subset of the nodes directly related to
      [n], ie a subset of [direct_uses] U [direct_dpds].
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  val iter_nodes : ((PdgTypes.Node.t -> unit) -> t -> unit) ref
  (** apply a given function to all the PDG nodes
      @raise Bottom if given PDG is bottom.
      @raise Top if the given pdg is top. *)

  (** {3 Pretty printing} *)

  val extract : (t -> string -> unit) ref
  (** Pretty print pdg into a dot file.
      @see <../pdg/index.html> PDG internal documentation. *)

  val pretty_node : (bool -> Format.formatter -> PdgTypes.Node.t -> unit) ref
  (** Pretty print information on a node : with [short=true], only the id
      of the node is printed.. *)

  val pretty_key : (Format.formatter -> PdgIndex.Key.t -> unit) ref
  (** Pretty print information on a node key *)

  val pretty : (?bw:bool -> Format.formatter -> t -> unit) ref
  (** For debugging... Pretty print pdg information.
      Print codependencies rather than dependencies if [bw=true]. *)

end


(** Signature common to some Inout plugin options. The results of
    the computations are available on a per function basis. *)
module type INOUTKF = sig

  type t

  val self_internal: State.t ref
  val self_external: State.t ref

  val compute : (kernel_function -> unit) ref

  val get_internal : (kernel_function -> t) ref
  (** Inputs/Outputs with local and formal variables *)

  val get_external : (kernel_function -> t) ref
  (** Inputs/Outputs without either local or formal variables *)

  (** {3 Pretty printing} *)

  val display : (Format.formatter -> kernel_function -> unit) ref
  val pretty : Format.formatter -> t -> unit

end

(** Signature common to inputs and outputs computations. The results
    are also available on a per-statement basis. *)
module type INOUT = sig
  include INOUTKF

  val statement : (stmt -> t) ref
  val kinstr : kinstr -> t option
end

(** State_builder.of read inputs.
    That is over-approximation of zones read by each function.
    @see <../inout/Inputs.html> internal documentation. *)
module Inputs : sig

  include INOUT with type t = Locations.Zone.t

  val expr : (stmt -> exp -> t) ref

  val self_with_formals: State.t ref

  val get_with_formals : (kernel_function -> t) ref
  (** Inputs with formals and without local variables *)

  val display_with_formals: (Format.formatter -> kernel_function -> unit) ref

end

(** State_builder.of outputs.
    That is over-approximation of zones written by each function.
    @see <../inout/Outputs.html> internal documentation. *)
module Outputs : sig
  include INOUT with type t = Locations.Zone.t
  val display_external : (Format.formatter -> kernel_function -> unit) ref
end

(** State_builder.of operational inputs.
    That is:
    - over-approximation of zones whose input values are read by each function,
      State_builder.of sure outputs
    - under-approximation of zones written by each function.
      @see <../inout/Context.html> internal documentation. *)
module Operational_inputs : sig
  include INOUTKF with type t = Inout_type.t
  val get_internal_precise: (?stmt:stmt -> kernel_function -> Inout_type.t) ref
  (** More precise version of [get_internal] function. If [stmt] is
      specified, and is a possible call to the given kernel_function,
      returns the operational inputs for this call. *)

  (**/**)
  (* Internal use *)
  module Record_Inout_Callbacks:
    Hook.Iter_hook with type param = Value_types.callstack * Inout_type.t
  (**/**)
end


(**/**)
(** Do not use yet.
    @see <../inout/Derefs.html> internal documentation. *)
module Derefs : INOUT with type t = Locations.Zone.t
(**/**)

(** {3 GUI} *)

(** This function should be called from time to time by all analysers taking
    time. In GUI mode, this will make the interface reactive.
    @plugin development guide
    @deprecated 21.0-Scandium *)
val progress: (unit -> unit) ref
[@@ deprecated "Use Db.yield instead."]

(** Registered daemon on progress. *)
type daemon

(**
   [on_progress ?debounced ?on_delayed trigger] registers [trigger] as new
   daemon to be executed on each {!yield}.
   @param debounced the least amount of time between two successive calls to the
   daemon, in milliseconds (default is 0ms).
   @param on_delayed the callback invoked as soon as the time since the last
   {!yield} is greater than [debounced] milliseconds (or 100ms at least).
*)
val on_progress :
  ?debounced:int -> ?on_delayed:(int -> unit) -> (unit -> unit) -> daemon

(** Unregister the [daemon]. *)
val off_progress : daemon -> unit

(** Trigger all daemons immediately. *)
val flush : unit -> unit

(** Trigger all registered daemons (debounced).
    This function should be called from time to time by all analysers taking
    time. In GUI mode, this will make the interface reactive. *)
val yield : unit -> unit

(** Interrupt the currently running job at the next call to {!yield} as a
    [Cancel] exception is raised. *)
val cancel : unit -> unit

(**
   [with_progress ?debounced ?on_delayed trigger job data] executes the given
   [job] on [data] while registering [trigger] as temporary (debounced) daemon.
   The daemon is finally unregistered at the end of the computation.

   Illustrative example, where [...] is the debounced time:
   {[
     job data :    |<-------------------------------------------------->|<daemon removed>
                   yields   :       x   x  x x    x             x   x    x   xxx xxx
         trigger  :       |..........   |..........   |..........  |.........
     delayed  :                                   !
         notes    :      (1)           (2)           (3)
   ]}

   + First yield, normal trigger.
   + Debounced yields leads to this second trigger.
   + Delayed warning invoked since there was no yield for more than debounced period.

   Raises every exception raised during the execution of [job] on [data].

   @param debounced the least amount of time, in milliseconds, between two
   successive calls to the daemon (default is 0ms).
   @param on_delayed the callback invoked as soon as the time since the last
   [yield] is greater than [debounced] milliseconds (or 100ms at least).
*)
val with_progress :
  ?debounced:int -> ?on_delayed:(int -> unit) ->
  (unit -> unit) -> ('a -> 'b) -> 'a -> 'b

(**
   Pauses the currently running process for the specified time, in milliseconds.
   Registered daemons, if any, will be regularly triggered during this waiting
   time at a reasonable period with respect to their debouncing constraints.
*)
val sleep : int -> unit

(** This exception may be raised by {!yield} to interrupt computations. *)
exception Cancel

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
