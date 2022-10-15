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

(* ---------------------------------------------------------------------- *)
(** {1 Global setting.} *)

(** Internal state of the slicing tool from project viewpoints. *)
val self : State.t

(* ---------------------------------------------------------------------- *)

(** {2 Functions with journalized side effects } *)

(** Set the used slicing modes. *)
val set_modes :
  ?calls:SlicingParameters.Mode.Calls.t ->
  ?callers:SlicingParameters.Mode.Callers.t ->
  ?sliceUndef:SlicingParameters.Mode.SliceUndef.t ->
  ?keepAnnotations:SlicingParameters.Mode.KeepAnnotations.t -> unit -> unit

(* ---------------------------------------------------------------------- *)

(** {1 Slicing project management.} *)
module Project : sig

  (** {2 Functions with journalized side effects } *)

  (** Init/reset a slicing project. *)
  val reset_slicing : unit -> unit

  (** Change the slicing level of this function
      (see the [-slicing-level] option documentation to know the meaning of
      the number)
      @raise SlicingTypes.ExternalFunction if [kf] has no definition.
      @raise SlicingTypes.WrongSlicingLevel if [n] is not valid. *)
  val change_slicing_level : Cil_types.kernel_function -> int -> unit

  (** Build a new [Db.Project.t] from all [Slice.t] of a project.
      Can optionally specify how to name the sliced functions
      by defining [f_slice_names].
      [f_slice_names kf src_visi num_slice] has to return the name
      of the exported functions based on the source function [kf].
      - [src_visi] tells if the source function name is used
                   (if not, it can be used for a slice)
      - [num_slice] gives the number of the slice to name.
        The entry point function is only exported once :
        it is VERY recommended to give to it its original name,
        even if it is sliced. *)
  val extract :
    ?f_slice_names:(Cil_types.kernel_function -> bool -> int -> string) ->
    string -> Project.t

  (** Print a representation of the slicing project (call graph)
      in a dot file which name is the given string. *)
  val print_dot : filename:string -> title:string -> unit

  (** {2 No needs of Journalization} *)

  val default_slice_names : Cil_types.kernel_function -> bool -> int -> string

  (** Return [true] iff the source function is called (even indirectly via
      transitivity) from a [Slice.t]. *)
  val is_called : Cil_types.kernel_function -> bool

  (** Return [true] iff the source function has persistent selection *)
  val has_persistent_selection : Cil_types.kernel_function -> bool

  (** Return [true] if the source function is directly (even via pointer
      function) called from a [Slice.t]. *)
  val is_directly_called_internal : Cil_types.kernel_function -> bool

  (** {2 Debug} *)

  val pretty : Format.formatter -> unit

end

(* ---------------------------------------------------------------------- *)

(** {1 Access to slicing results.} *)
module Mark : sig

  (** Abstract data type for mark value. *)
  type t = SlicingTypes.sl_mark

  (** For dynamic type checking and journalization. *)
  val dyn_t : t Type.t

  (** {2 No needs of Journalization} *)

  (** To construct a mark such as
      [(is_ctrl result, is_data result, isaddr result) = (~ctrl, ~data, ~addr)],
      [(is_bottom result) = false] and
      [(is_spare result) = not (~ctrl || ~data || ~addr)]. *)
  val make : data:bool -> addr:bool -> ctrl:bool -> t

  (** A total ordering function similar to the generic structural
      comparison function [compare].
      Can be used to build a map from [t] marks to, for example, colors for
      the GUI. *)
  val compare : t -> t -> int

  (** [true] iff the mark is empty: it is the only case where the associated
      element is invisible. *)
  val is_bottom : t -> bool

  (** Smallest visible mark. Usually used to mark element that need to be
      visible for compilation purpose, not really for the selected computations.
      That mark is related to transparent selection. *)
  val is_spare : t -> bool

  (** The element is used to control the program point of a selected data. *)
  val is_ctrl : t -> bool

  (** The element is used to compute selected data.
      Notice that a mark can be [is_data] and/or [is_ctrl] and/or [is_addr]
      at the same time. *)
  val is_data : t -> bool

  (** The element is used to compute the address of a selected data. *)
  val is_addr : t -> bool

  (** The mark [m] related to all statements of a source function [kf].
      Property : [is_bottom (get_from_func proj kf) =
                     not (Project.is_called proj kf) ] *)
  val get_from_src_func : Cil_types.kernel_function -> t

  (** {2 Debug} *)

  val pretty : Format.formatter -> t -> unit

end

(* ---------------------------------------------------------------------- *)

(** {1 Slicing selections.} *)
module Select : sig

  (** Internal selection. *)
  type t = SlicingTypes.sl_select

  (** For dynamic type checking and journalization. *)
  val dyn_t : t Type.t

  (** Set of colored selections. *)
  type set = SlicingCmds.set

  (** For dynamic type checking and journalization. *)
  val dyn_set : set Type.t

  (** {2 Selectors.} *)

  (** Empty selection. *)
  val empty_selects : set

  (** {3 Statement selectors.} *)

  (** To select a statement. *)
  val select_stmt :
    set -> spare:bool -> Cil_datatype.Stmt.t -> Cil_types.kernel_function -> set

  (** To select a statement reachability.
      Note: add also a transparent selection on the whole statement. *)
  val select_stmt_ctrl :
    set -> spare:bool -> Cil_datatype.Stmt.t -> Cil_types.kernel_function -> set

  (** To select rw accesses to lvalues (given as string) related to a statement.
      Variables of [~rd] and [~wr] string are bounded relatively to the whole
      scope of the function.
      The interpretation of the address of the lvalues is done just before the
      execution of the statement [~eval].
      The selection preserve the [~rd] and ~[wr] accesses contained into the
      statement [ki].
      Note: add also a transparent selection on the whole statement. *)
  val select_stmt_lval_rw :
    set ->
    Mark.t ->
    rd:Datatype.String.Set.t ->
    wr:Datatype.String.Set.t ->
    Cil_datatype.Stmt.t ->
    eval:Cil_datatype.Stmt.t -> Cil_types.kernel_function -> set

  (** To select lvalues (given as string) related to a statement.
      Variables of [lval_str] string are bounded relatively to the whole scope
      of the function.
      The interpretation of the address of the lvalue is done just before the
      execution of the statement [~eval].
      The selection preserve the value of these lvalues before or after (c.f.
      boolean [~before]) the statement [ki].
      Note: add also a transparent selection on the whole statement. *)
  val select_stmt_lval :
    set ->
    Mark.t ->
    Datatype.String.Set.t ->
    before:bool ->
    Cil_datatype.Stmt.t ->
    eval:Cil_datatype.Stmt.t -> Cil_types.kernel_function -> set

  (** To select a zone value related to a statement.
      Note: add also a transparent selection on the whole statement. *)
  val select_stmt_zone :
    set ->
    Mark.t ->
    Locations.Zone.t ->
    before:bool ->
    Cil_types.stmt -> Cil_types.kernel_function -> set

  (** To select a predicate value related to a statement.
      Note: add also a transparent selection on the whole statement. *)
  val select_stmt_term :
    set ->
    Mark.t ->
    Cil_types.term ->
    Cil_types.stmt -> Cil_types.kernel_function -> set

  (** To select a predicate value related to a statement.
      Note: add also a transparent selection on the whole statement. *)
  val select_stmt_pred :
    set ->
    Mark.t ->
    Cil_types.predicate ->
    Cil_types.stmt -> Cil_types.kernel_function -> set

  (** To select the annotations related to a statement.
      Note: add also a transparent selection on the whole statement. *)
  val select_stmt_annot :
    set ->
    Mark.t ->
    spare:bool ->
    Cil_types.code_annotation ->
    Cil_types.stmt -> Cil_types.kernel_function -> set

  (** To select the annotations related to a statement.
      Note: add also a transparent selection on the whole statement. *)
  val select_stmt_annots :
    set ->
    Mark.t ->
    spare:bool ->
    threat:bool ->
    user_assert:bool ->
    slicing_pragma:bool ->
    loop_inv:bool ->
    loop_var:bool -> Cil_datatype.Stmt.t -> Cil_types.kernel_function -> set

  (** {3 Function selectors.} *)

  (** To select rw accesses to lvalues (given as a string) related to a
      function.
      Variables of [~rd] and [~wr] string are bounded relatively to the whole
      scope of the function.
      The interpretation of the address of the lvalues is done just before the
      execution of the statement [~eval].
      The selection preserve the value of these lvalues into the whole project.
  *)
  val select_func_lval_rw :
    set -> Mark.t -> rd:Datatype.String.Set.t -> wr:Datatype.String.Set.t ->
    eval:Cil_datatype.Stmt.t -> Cil_types.kernel_function -> set

  (** To select lvalues (given as a string) related to a function.
      Variables of [lval_str] string are bounded relatively to the scope of the
      first statement of [kf].
      The interpretation of the address of the lvalues is done just before the
      execution of the first statement [kf].
      The selection preserve the value of these lvalues before execution of the
      return statement. *)
  val select_func_lval :
    set -> Mark.t -> Datatype.String.Set.t -> Cil_types.kernel_function -> set

  (** To select an output zone related to a function. *)
  val select_func_zone :
    set -> Mark.t -> Locations.Zone.t -> Cil_types.kernel_function -> set

  (** To select the function result (returned value). *)
  val select_func_return : set -> spare:bool -> Cil_types.kernel_function -> set

  (** To select every calls to the given function, i.e. the call keeps its
      semantics in the slice. *)
  val select_func_calls_to :
    set -> spare:bool -> Cil_types.kernel_function -> set

  (** To select every calls to the given function without the selection of its
      inputs/outputs. *)
  val select_func_calls_into :
    set -> spare:bool -> Cil_types.kernel_function -> set

  (** To select the annotations related to a function. *)
  val select_func_annots :
    set -> Mark.t -> spare:bool -> threat:bool -> user_assert:bool ->
    slicing_pragma:bool -> loop_inv:bool -> loop_var:bool ->
    Cil_types.kernel_function -> set

  (** {3 Pdg selectors.} *)

  val select_pdg_nodes :
    set -> Mark.t -> PdgTypes.Node.t list -> Cil_types.kernel_function -> set

  (** {3 Internal use only} *)

  (** The function related to an internal selection. *)
  val get_function : t -> Cil_types.kernel_function

  (** The function related to an internal selection. *)
  val merge_internal : t -> t -> t

  val add_to_selects_internal : t -> set -> set

  val iter_selects_internal : (t -> unit) -> set -> unit

  val fold_selects_internal :  (('a -> t -> 'a) -> 'a -> set -> 'a)

  (** Internally used to select a statement :
      - if [is_ctrl_mark m],
        propagate ctrl_mark on ctrl dependencies of the statement
      - if [is_addr_mark m],
        propagate addr_mark on addr dependencies of the statement
      - if [is_data_mark m],
        propagate data_mark on data dependencies of the statement
        Marks the node with a spare_mark and propagate so that the dependencies
        that were not selected yet will be marked spare.
        When the statement is a call, its functional inputs/outputs are also
        selected (The call is still selected even it has no output).
        When the statement is a composed one (block, if, etc...),
        all the sub-statements are selected.
        @raise SlicingTypes.NoPdg when the Pdg cannot be computed. *)
  val select_stmt_internal :
    Cil_types.kernel_function -> ?select:t -> Cil_types.stmt -> Mark.t -> t

  val select_label_internal :
    Cil_types.kernel_function ->
    ?select:t -> Cil_types.logic_label -> Mark.t -> t

  (** Internally used to select a statement call without its
      inputs/outputs so that it doesn't select the statements computing the
      inputs of the called function as [select_stmt_internal] would do.
      Raise [Invalid_argument] when the [stmt] isn't a call.
      @raise SlicingTypes.NoPdg when the Pdg cannot be computed. *)
  val select_min_call_internal :
    Cil_types.kernel_function -> ?select:t -> Cil_types.stmt -> Mark.t -> t

  (** Internally used to select a zone value at a program point.
      @raise SlicingTypes.NoPdg when the Pdg cannot be computed. *)
  val select_stmt_zone_internal :
    Cil_types.kernel_function ->
    ?select:t ->
    Cil_types.stmt -> before:bool -> Locations.Zone.t -> Mark.t -> t

  (** Internally used to select a zone value at the beginning of a function.
      For a defined function, it is similar to [select_stmt_zone_internal]
      with the initial statement, but it can also be used for undefined
      functions.
      @raise SlicingTypes.NoPdg when the Pdg cannot be computed. *)
  val select_zone_at_entry_point_internal :
    Cil_types.kernel_function -> ?select:t -> Locations.Zone.t -> Mark.t -> t

  (** Internally used to select a zone value at the end of a function.
      For a defined function, it is similar to [select_stmt_zone_internal]
      with the return statement, but it can also be used for undefined
      functions.
      @raise SlicingTypes.NoPdg when the Pdg cannot be computed. *)
  val select_zone_at_end_internal :
    Cil_types.kernel_function -> ?select:t -> Locations.Zone.t -> Mark.t -> t

  (** Internally used to select the statements that modify the
      given zone considered as in output.
      Be careful that it is NOT the same as selecting the zone at the end!
      The 'undef' zone is not propagated...
      @raise SlicingTypes.NoPdg when the Pdg cannot be computed. *)
  val select_modified_output_zone_internal :
    Cil_types.kernel_function -> ?select:t -> Locations.Zone.t -> Mark.t -> t

  (** Internally used to select a statement reachability :
      Only propagate a ctrl_mark on the statement control dependencies.
      @raise SlicingTypes.NoPdg when the Pdg cannot be computed. *)
  val select_stmt_ctrl_internal :
    Cil_types.kernel_function -> ?select:t -> Cil_types.stmt -> t

  val select_entry_point_internal :
    Cil_types.kernel_function -> ?select:t -> Mark.t -> t

  val select_return_internal :
    Cil_types.kernel_function -> ?select:t -> Mark.t -> t

  val select_decl_var_internal :
    Cil_types.kernel_function -> ?select:t -> Cil_types.varinfo -> Mark.t -> t

  (** Internally used to select PDG nodes :
      - if [is_ctrl_mark m],
        propagate ctrl_mark on ctrl dependencies of the statement
      - if [is_addr_mark m],
        propagate addr_mark on addr dependencies of the statement
      - if [is_data_mark m],
        propagate data_mark on data dependencies of the statement
        Marks the node with a spare_mark and propagate so that
        the dependencies that were not selected yet will be marked spare. *)
  val select_pdg_nodes_internal :
    Cil_types.kernel_function ->
    ?select:t -> PdgTypes.Node.t list -> Mark.t -> t

  (** {2 Debug} *)

  val pretty : Format.formatter -> t -> unit

end

(* ---------------------------------------------------------------------- *)

(** {1 Slice} *)
module Slice : sig

  type t = SlicingTypes.sl_fct_slice
  val dyn_t : t Type.t

  (** {2 Functions with journalized side effects } *)

  val create : Cil_types.kernel_function -> t

  val remove : t -> unit

  val remove_uncalled : unit -> unit

  (** {2 No needs of Journalization} *)

  val get_all : Cil_types.kernel_function -> t list

  val get_function : t -> Cil_types.kernel_function

  val get_callers : t -> t list

  val get_called_slice : t -> Cil_types.stmt -> t option

  val get_called_funcs : t -> Cil_types.stmt -> Cil_types.kernel_function list

  val get_mark_from_stmt : t -> Cil_types.stmt -> Mark.t

  val get_mark_from_label : t -> Cil_types.stmt -> Cil_types.label -> Mark.t

  val get_mark_from_local_var : t -> Cil_types.varinfo -> Mark.t

  val get_mark_from_formal : t -> Cil_datatype.Varinfo.t -> Mark.t

  val get_user_mark_from_inputs : t -> Mark.t

  val get_num_id : t -> int

  val from_num_id : Cil_types.kernel_function -> int -> t

  (** {2 Debug} *)

  val pretty : Format.formatter -> t -> unit

end

(* ---------------------------------------------------------------------- *)

(** {1 Slicing request} *)
module Request : sig

  (** {2 Functions with journalized side effects } *)

  val apply_all : propagate_to_callers:bool -> unit

  val apply_all_internal : unit -> unit

  val apply_next_internal : unit -> unit

  val propagate_user_marks : unit -> unit

  val copy_slice : Slice.t -> Slice.t

  val split_slice : Slice.t -> Slice.t list

  val merge_slices : Slice.t -> Slice.t -> replace:bool -> Slice.t

  val add_call_slice : caller:Slice.t -> to_call:Slice.t -> unit

  val add_call_fun : caller:Slice.t -> to_call:Cil_types.kernel_function -> unit

  val add_call_min_fun :
    caller:Slice.t -> to_call:Cil_types.kernel_function -> unit

  val add_selection : Select.set -> unit

  val add_persistent_selection : Select.set -> unit

  val add_persistent_cmdline : unit -> unit

  (** {2 No needs of Journalization} *)

  val is_request_empty_internal : unit -> bool

  val add_slice_selection_internal : Slice.t -> Select.t -> unit

  val add_selection_internal : Select.t -> unit

  (** {2 Debug} *)

  val pretty : Format.formatter -> unit

end

(* ---------------------------------------------------------------------- *)
(** {1 Global data management} *)

val split_slice : Slice.t -> Slice.t list

val merge_slices : Slice.t -> Slice.t -> replace:bool -> Slice.t

val copy_slice : Slice.t -> Slice.t

(* -- end -------------------------------------------------------------- *)
