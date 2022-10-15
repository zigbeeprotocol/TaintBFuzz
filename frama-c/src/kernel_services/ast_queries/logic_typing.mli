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

(** Logic typing and logic environment. *)

open Cil_types

(** Relation operators conversion
    @since Nitrogen-20111001
*)
val type_rel: Logic_ptree.relation -> Cil_types.relation

(** Arithmetic binop conversion. Addition and Subtraction are always
    considered as being used on integers. It is the responsibility of the
    user to introduce PlusPI, MinusPI and MinusPP where needed.
    @since Nitrogen-20111001
*)
val type_binop: Logic_ptree.binop -> Cil_types.binop

val unescape: string -> string
val wcharlist_of_string: string -> int64 list

val is_arithmetic_type: Cil_types.logic_type -> bool
val is_integral_type: Cil_types.logic_type -> bool
val is_set_type: Cil_types.logic_type -> bool
val is_array_type: Cil_types.logic_type -> bool
val is_pointer_type: Cil_types.logic_type -> bool

(** @since Aluminium-20160501 *)
val is_list_type: Cil_types.logic_type -> bool

(** @since Aluminium-20160501 *)
val type_of_list_elem : logic_type -> logic_type

val type_of_pointed: logic_type -> logic_type
val type_of_array_elem: logic_type -> logic_type
val type_of_set_elem: logic_type -> logic_type

val ctype_of_pointed: logic_type -> typ
val ctype_of_array_elem: logic_type -> typ

val arithmetic_conversion:
  Cil_types.logic_type -> Cil_types.logic_type -> Cil_types.logic_type

(** Local logic environment *)
module Lenv : sig
  type t
  val empty : unit -> t

  val add_var: string -> Cil_types.logic_var -> t -> t
  val add_type_var: string -> Cil_types.logic_type -> t -> t
  val add_logic_info: string -> Cil_types.logic_info -> t -> t
  val add_logic_label: string -> Cil_types.logic_label -> t -> t

  val find_var: string -> t-> Cil_types.logic_var
  val find_type_var: string -> t -> Cil_types.logic_type
  val find_logic_info: string -> t -> Cil_types.logic_info
  val find_logic_label: string -> t -> Cil_types.logic_label

end

type type_namespace = Typedef | Struct | Union | Enum
(** The different namespaces a C type can belong to, used when we are searching
    a type by its name. *)

module Type_namespace: Datatype.S with type t = type_namespace

(** Functions that can be called when type-checking an extension of ACSL. *)
type typing_context = {
  is_loop: unit -> bool;
  anonCompFieldName : string;
  conditionalConversion : typ -> typ -> typ;
  find_macro : string -> Logic_ptree.lexpr;
  find_var : ?label:string -> string -> logic_var;
  (** the label argument is a C label (obeying the restrictions
      of which label can be present in a \at). If present, the scope for
      searching local C variables is the one of the statement with
      the corresponding label. *)
  find_enum_tag : string -> exp * typ;
  find_comp_field: compinfo -> string -> offset;
  find_type : type_namespace -> string -> typ;
  find_label : string -> stmt ref;
  remove_logic_function : string -> unit;
  remove_logic_info: logic_info -> unit;
  remove_logic_type: string -> unit;
  remove_logic_ctor: string -> unit;
  add_logic_function: logic_info -> unit;
  add_logic_type: string -> logic_type_info -> unit;
  add_logic_ctor: string -> logic_ctor_info -> unit;
  find_all_logic_functions: string -> logic_info list;
  find_logic_type: string -> logic_type_info;
  find_logic_ctor: string -> logic_ctor_info;
  pre_state:Lenv.t;
  post_state:termination_kind list -> Lenv.t;
  assigns_env: Lenv.t;
  silent: bool;
  logic_type:
    typing_context -> location -> Lenv.t ->
    Logic_ptree.logic_type -> Cil_types.logic_type ;
  type_predicate:
    typing_context -> Lenv.t -> Logic_ptree.lexpr -> predicate;
  (** typechecks a predicate. Note that the first argument is itself a
      [typing_context], which allows for open recursion. Namely, it is
      possible for the extension to change the type-checking functions for
      the sub-nodes of the parsed tree, and not only for the toplevel [lexpr].

      @plugin development guide
  *)
  type_term:
    typing_context -> Lenv.t -> Logic_ptree.lexpr -> term;
  type_assigns:
    typing_context ->
    accept_formal:bool ->
    Lenv.t -> Logic_ptree.assigns -> assigns;
  error: 'a 'b. location -> ('a,Format.formatter,unit,'b) format4 -> 'a;

  on_error: 'a 'b. ('a -> 'b) -> ((location * string) -> unit) -> 'a -> 'b
  (** [on_error f rollback x] will attempt to evaluate [f x]. If this triggers
      an error while in [-continue-annot-error] mode, [rollback (loc,cause)]
      will be executed (where [loc] is the location of the error and [cause]
      a text message indicating the issue) and the exception will be re-raised.

      @since Chlorine-20180501
      @before 25.0-Manganese [rollback] didn't take [loc] and [cause] as argument
  *)
}

module Make
    (C :
     sig
       val is_loop: unit -> bool
       (** whether the annotation we want to type is contained in a loop.
           Only useful when creating objects of type [code_annotation]. *)

       val anonCompFieldName : string
       val conditionalConversion : typ -> typ -> typ
       val find_macro : string -> Logic_ptree.lexpr
       val find_var : ?label:string -> string -> logic_var
       (** see corresponding field in {!Logic_typing.typing_context}. *)

       val find_enum_tag : string -> exp * typ
       val find_type : type_namespace -> string -> typ
       val find_comp_field: compinfo -> string -> offset
       val find_label : string -> stmt ref

       val remove_logic_function : string -> unit
       val remove_logic_info: logic_info -> unit
       val remove_logic_type: string -> unit
       val remove_logic_ctor: string -> unit

       val add_logic_function: logic_info -> unit
       val add_logic_type: string -> logic_type_info -> unit
       val add_logic_ctor: string -> logic_ctor_info -> unit

       val find_all_logic_functions : string -> Cil_types.logic_info list
       val find_logic_type: string -> logic_type_info
       val find_logic_ctor: string -> logic_ctor_info

       (** What to do when we have a term of type Integer in a context
           expecting a C integral type.
           @raise Failure to reject such conversion
           @since Nitrogen-20111001
       *)
       val integral_cast: Cil_types.typ -> Cil_types.term -> Cil_types.term

       (** raises an error at the given location and with the given message.
           @since Magnesium-20151001 *)
       val error: location -> ('a,Format.formatter,unit, 'b) format4 -> 'a

       (** see {!Logic_typing.typing_context}. *)
       val on_error: ('a -> 'b) -> ((location * string) -> unit) -> 'a -> 'b

     end) :
sig

  (** @since Nitrogen-20111001 *)
  val type_of_field:
    location -> string -> logic_type -> (term_offset * logic_type)

  (**
     @param explicit true if the cast is present in original source.
            defaults to false
     @since Nitrogen-20111001
  *)
  val mk_cast:
    ?explicit:bool -> Cil_types.term -> Cil_types.logic_type -> Cil_types.term

  (** type-checks a term. *)
  val term : Lenv.t -> Logic_ptree.lexpr -> term

  val predicate : Lenv.t -> Logic_ptree.lexpr -> predicate

  (** [code_annot loc behaviors rt annot] type-checks an in-code annotation.
      @param loc current location
      @param behaviors list of existing behaviors
      @param rt return type of current function
      @param annot the annotation
  *)
  val code_annot :
    Cil_types.location -> string list ->
    Cil_types.logic_type -> Logic_ptree.code_annot -> code_annotation

  val type_annot :
    location -> Logic_ptree.type_annot -> logic_info

  val model_annot :
    location -> Logic_ptree.model_annot -> model_info

  val annot : Logic_ptree.decl -> global_annotation

  (** [funspec behaviors f prms typ spec] type-checks a function contract.
      @param behaviors list of existing behaviors (outside of the current
      spec, e.g. in the spec of the corresponding declaration when type-checking
      the spec of a definition)
      @param f the function
      @param prms its parameters
      @param its type
      @param spec the spec to typecheck
  *)
  val funspec :
    string list ->
    varinfo -> (varinfo list) option -> typ -> Logic_ptree.spec -> funspec

end

(** append the Old and Post labels in the environment *)
val append_old_and_post_labels: Lenv.t -> Lenv.t

(** appends the Here label in the environment *)
val append_here_label: Lenv.t -> Lenv.t

(** appends the "Pre" label in the environment *)
val append_pre_label: Lenv.t -> Lenv.t

(** appends the "Init" label in the environment
    @since Sodium-20150201
*)
val append_init_label: Lenv.t -> Lenv.t


(** adds a given variable in local environment. *)
val add_var: string -> logic_var -> Lenv.t -> Lenv.t

(** add [\result] in the environment. *)
val add_result: Lenv.t -> logic_type -> Lenv.t

(** enter a given post-state. *)
val enter_post_state: Lenv.t -> termination_kind -> Lenv.t

(** enter a given post-state and put [\result] in the env.
    NB: if the kind of the post-state is neither [Normal] nor [Returns],
    this is not a normal ACSL environment. Use with caution.
*)
val post_state_env: termination_kind -> logic_type -> Lenv.t


(** {2 Internal use} *)

val set_extension_handler:
  is_extension:(string -> bool) ->
  typer:(string -> typing_context -> location -> Logic_ptree.lexpr list ->
         (bool * acsl_extension_kind)) ->
  typer_block:(string -> typing_context ->
               Filepath.position * Filepath.position ->
               string * Logic_ptree.extended_decl list ->
               bool * Cil_types.acsl_extension_kind) ->
  unit
(** Used to setup references related to the handling of ACSL extensions.
    If your name is not [Acsl_extension], do not call this
    @since 21.0-Scandium
*)

val get_typer :
  string ->
  typing_context:typing_context ->
  loc:Filepath.position * Filepath.position ->
  Logic_ptree.lexpr list -> bool * Cil_types.acsl_extension_kind

val get_typer_block:
  string ->
  typing_context:typing_context ->
  loc:Logic_ptree.location ->
  string * Logic_ptree.extended_decl list ->
  bool * Cil_types.acsl_extension_kind

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
