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

(** [string_of_typ t] returns a name generated from the given [t]. This is
    basically the C name of the type except that:
    - separator is ["_"],
    - [unsigned] is ["u"]
    - [[SIZE]] is ["arrSIZE"],
    - [*] is ["ptr"],
    - [enum] is ["e_"],
    - [struct] is ["st_"],
    - [union] is ["un_"]

    For example for: [struct X ( * ) [10]], the name is ["ptr_arr10_st_X"].
*)
val string_of_typ: typ -> string

(** Returns the type of pointed for a give logic_type *)
val ttype_of_pointed: logic_type -> logic_type


(** {2 C} *)

(** For a type [T], returns [T*] *)
val ptr_of: typ -> typ

(** For a type [T], returns [T const] *)
val const_of: typ -> typ

(** Finds and returns [size_t] *)
val size_t: unit -> typ

(** Create a function definition from a name and a type
    - [vdefined] is positionned to [true]
    - formals are registered to FormalsDecl
*)
val prepare_definition: string -> typ -> fundec

(** [call_function ret_lval vi args] creates an instruction
    - [(ret_lval = ) vi.vname(args)].
*)
val call_function: lval option -> varinfo -> exp list -> instr


(** {2 Terms} *)

(** Builds a term from a varinfo *)
val cvar_to_tvar: varinfo -> term

(** [tunref_range ~loc ptr len] builds [*(ptr + (0 .. len-1))] *)
val tunref_range: ?loc:location -> term -> term -> term

(** [tunref_range ~loc ptr bytes_len] same as [tunref_range] except that length
    is provided in bytes.
*)
val tunref_range_bytes_len: ?loc:location -> term -> term -> term

(** [tplus ~loc t1 t2] builds [t1+t2] *)
val tplus: ?loc:location -> term -> term -> term

(** [tminus ~loc t1 t2] builds [t1-t2] *)
val tminus: ?loc:location -> term -> term -> term

(** [tdivide ~loc t1 t2] builds [t1/t2] *)
val tdivide: ?loc:location -> term -> term -> term


(** {2 Predicates} *)

(** [pbounds_incl_excl ~loc low v up] builds [low <= v < up]. *)
val pbounds_incl_excl: ?loc:location -> term -> term -> term -> predicate

(** [plet_len_div_size ~loc ~name_ext ltyp bytes_len pred] buils a predicate:
    - [\let name = bytes_len / sizeof(ltyp) ; < pred name >]

    with [name = "__fc_<name_ext>len"]. For example, if [pred len] generates an
    ACSL predicate:
    - [\forall int x ; 0 <= x < len ==> p[x] == 0],

    [ltyp] is [int], and [bytes_len] is 16, it generates:
    - [\let __fc_len = bytes_len / sizeof(ltyp) ;
       \forall int x ; 0 <= x < __fc_len ==> p[x] == 0].

    Parameters:
    - [loc] defaults to [Cil_datatype.Location.unknown]
    - [name_ext] defaults to [""]
    - [ltyp] must be a logic C type
    - [bytes_len] is a value in bytes that should be divided by the [sizeof(ltyp)]
    - if the elements contains structures they cannot have flexible array member
*)
val plet_len_div_size:
  ?loc:location -> ?name_ext:string ->
  logic_type -> term -> (term -> predicate) -> predicate

(** [punfold_all_elems_eq ~loc p1 p2 len] builds a predicate:
    - [\forall integer j1 ; 0 <= j1 < len ==> p1[j1] == p2[j1]].

    If [p1[j1]] is itself an array, it recursively builds a predicate:
    - [\forall integer j2 ; 0 <= j2 < len_of_array ==> ...].

    Parameters:
    - [p1] and [p2] must be pointers to the same type
*)
val punfold_all_elems_eq: ?loc:location -> term -> term -> term -> predicate

(** [punfold_all_elems_pred ~loc ptr len pred] builds a predicate:
    - [\forall integer j ; 0 <= j1 < len ==> < pred (\*(ptr + j1)) >].

    If [ptr[j1]] is a compound type (array or structure), it recursively builds
    a predicate on each element (either by introducing a new [\forall] for
    arrays or a conjunction for structure fields).

    - [ptr] must be a pointer
    - [pred] must be applicable on simple types or pointers
    - if the elements contains structures they cannot have flexible array member
*)
val punfold_all_elems_pred:
  ?loc:location -> term -> term ->
  (?loc: location -> term -> predicate) -> predicate

(** [punfold_flexible_struct_pred ~loc struct bytes_len pred].

    For a [struct] term of C type [struct X { ... ; Type a[]; };], it generates
    a predicate:
    - [\let __fc_len = (bytes_len - sizeof(struct X)) / sizeof(Type) ;
        < pred on struct fields > &&
        \forall integer j ; 0 <= j <= __fc_len ==> < pred on struct.a[j] >]

    If met components are compound, it behaves like [punfold_all_elems_pred].

    Parameters:
    - [struct] must be a (term) structure with a flexible array member
    - [bytes_len] is the length of the structure in bytes
    - [pred] must be applicable on simple types or pointers
*)
val punfold_flexible_struct_pred:
  ?loc:location -> term -> term ->
  (?loc: location -> term -> predicate) -> predicate

(** [pvalid_len_bytes ~loc label ptr bytes_len] generates a predicate
    - [\valid{label}(ptr + (0 .. (len_bytes/sizeof(\*ptr))))].

    Parameters:
    - [ptr] must be a term of pointer type.
*)
val pvalid_len_bytes: ?loc:location -> logic_label -> term -> term -> predicate

(** [pvalid_read_len_bytes ~loc label ptr bytes_len] generates a predicate
    - [\valid_read{label}(ptr + (0 .. (len_bytes/sizeof(\*ptr))))].

    Parameters:
    - [ptr] must be a term of pointer type.
*)
val pvalid_read_len_bytes:
  ?loc:location -> logic_label -> term -> term -> predicate

(** [pcorrect_len_bytes ~loc ltyp bytes_len] returns a predicate
    [bytes_len % sizeof(ltyp) == 0].
*)
val pcorrect_len_bytes: ?loc:location -> logic_type -> term -> predicate

(** [pseparated_memories ~loc p1 len1 p2 len2] returns a predicate:
    - [\separated(p1 + (0 .. len1), p2 + (0 .. len2))]

    Parameters:
    - [p1] and [p2] must be of pointer type
*)
val pseparated_memories:
  ?loc:location -> term -> term -> term -> term -> predicate

(** {2 Specification} *)

(** Builds a behavior from its components. If a component is missing,
    it defaults to:
    - [name]: [Cil.default_behavior_name]
    - [requires], [ensures], [extension]: [[]]
    - [assigns]: = [WritesAny]
    - [alloc]: [FreeAllocAny]
*)
val make_behavior:
  ?name:string ->
  ?assumes:identified_predicate list ->
  ?requires:identified_predicate list ->
  ?ensures:(termination_kind * identified_predicate) list ->
  ?assigns:assigns ->
  ?alloc:allocation ->
  ?extension:acsl_extension list ->
  unit ->
  behavior

(** Builds a funspec from a list of behaviors.
    - [termination] defaults to [None]
    - [complete_disjoint] default to all disjoint, all complete
*)
val make_funspec:
  behavior list ->
  ?termination:identified_predicate option ->
  ?complete_disjoint:(string list list * string list list) ->
  unit ->
  funspec
