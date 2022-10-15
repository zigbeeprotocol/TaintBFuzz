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

(* -------------------------------------------------------------------------- *)
(* --- Constituant of the Server API                                      --- *)
(* -------------------------------------------------------------------------- *)

type plugin = Kernel | Plugin of string
type ident = private { plugin: plugin; package: string list; name: string; }

type jtype =
  | Jany
  | Jnull
  | Jboolean
  | Jnumber
  | Jstring
  | Jalpha (** string primarily compared without case *)
  | Jtag of string (** single constant string *)
  | Jkey of string (** kind of a string used for indexing *)
  | Jindex of string (** kind of an integer used for indexing *)
  | Joption of jtype
  | Jdict of jtype (** dictionaries *)
  | Jlist of jtype (** order does not matter *)
  | Jarray of jtype (** order matters *)
  | Jtuple of jtype list
  | Junion of jtype list
  | Jrecord of (string * jtype) list
  | Jdata of ident
  | Jenum of ident (** data that is an enum *)
  | Jself (** for (simply) recursive types *)

type fieldInfo = {
  fd_name: string;
  fd_type: jtype;
  fd_descr: Markdown.text;
}

type tagInfo = {
  tg_name: string;
  tg_label: Markdown.text;
  tg_descr: Markdown.text;
}

type paramInfo =
  | P_value of jtype
  | P_named of fieldInfo list

type requestInfo = {
  rq_kind: [ `GET | `SET | `EXEC ];
  rq_input: paramInfo ;
  rq_output: paramInfo ;
  rq_signals : string list;
}

type arrayInfo = {
  arr_key: string;
  arr_kind: jtype;
}

type declKindInfo =
  | D_signal
  | D_type of jtype
  | D_enum of tagInfo list
  | D_record of fieldInfo list
  | D_request of requestInfo
  | D_value of jtype
  | D_state of jtype
  | D_array of arrayInfo
  | D_safe of ident * jtype (* safe decoder *)
  | D_loose of ident * jtype (* loose decoder *)
  | D_order of ident * jtype (* natural ordering *)

type declInfo = {
  d_ident : ident;
  d_descr : Markdown.text;
  d_kind : declKindInfo;
}

type packageInfo = {
  p_plugin : plugin ;
  p_package : string list ;
  p_title : string ;
  p_descr : Markdown.text ;
  p_readme : string option ;
  p_content : declInfo list ;
}

(* -------------------------------------------------------------------------- *)
(* --- Pretty Printers                                                    --- *)
(* -------------------------------------------------------------------------- *)

val pp_plugin : Format.formatter -> plugin -> unit
val pp_pkgname : Format.formatter -> packageInfo -> unit
val pp_ident : Format.formatter -> ident -> unit
val pp_jtype : Format.formatter -> jtype -> unit

(* -------------------------------------------------------------------------- *)
(* --- Derived Names                                                      --- *)
(* -------------------------------------------------------------------------- *)

val derived : ?prefix:string -> ?suffix:string -> ident -> ident

module Derived :
sig
  val signal : ident -> ident
  val getter : ident -> ident
  val setter : ident -> ident
  val data : ident -> ident
  val fetch : ident -> ident
  val reload : ident -> ident
  val safe : ident -> ident
  val loose : ident -> ident
  val order : ident -> ident
  val decode : safe:bool -> ident -> ident
end

(* -------------------------------------------------------------------------- *)
(* --- Names Resolution                                                   --- *)
(* -------------------------------------------------------------------------- *)

module IdMap : Map.S with type key = ident

module Scope :
sig
  type t
  val create : plugin -> t
  val reserve : t -> string -> unit
  (** Must _not_ be call after [use] *)

  val declare : t -> ident -> unit
  (** Must _not_ be call after [use] *)

  val use : t -> ident -> unit
  val resolve : t -> string IdMap.t
end

val isRecursive : jtype -> bool
val visit_jtype : (ident -> unit) -> jtype -> unit
val visit_field: (ident -> unit) -> fieldInfo -> unit
val visit_param: (ident -> unit) -> paramInfo -> unit
val visit_request: (ident -> unit) -> requestInfo -> unit
val visit_dkind: (ident -> unit) -> declKindInfo -> unit
val visit_decl: (ident -> unit) -> declInfo -> unit
val visit_package_decl: (ident -> unit) -> packageInfo -> unit
val visit_package_used: (ident -> unit) -> packageInfo -> unit

(* -------------------------------------------------------------------------- *)
(* --- Server API                                                         --- *)
(* -------------------------------------------------------------------------- *)

type package

val package :
  ?plugin:string ->
  ?name:string ->
  title:string ->
  ?descr:Markdown.text ->
  ?readme:string ->
  unit -> package

(**
   Register the declaration in the Server API.
   This is only way to obtain identifiers.
   This ensures identifiers are declared before being used.
*)
val declare :
  package:package ->
  name:string ->
  ?descr:Markdown.text ->
  declKindInfo ->
  unit

(**
   Same as [declare] but returns the associated identifier.
*)
val declare_id :
  package:package ->
  name:string ->
  ?descr:Markdown.text ->
  declKindInfo ->
  ident

(**
   Replace the declaration for the given name in the package.
*)
val update :
  package:package ->
  name:string ->
  declKindInfo ->
  unit

val iter : (packageInfo -> unit) -> unit

(** Assigns non-classing names for each identifier. *)
val resolve : ?keywords: string list -> packageInfo -> string IdMap.t

val field : fieldInfo -> string * jtype
val name_of_pkg : ?sep:string -> plugin -> string list -> string
val name_of_pkginfo : ?sep:string -> packageInfo -> string
val name_of_package : ?sep:string -> package -> string
val name_of_ident : ?sep:string -> ident -> string

(* -------------------------------------------------------------------------- *)
(* --- Markdown Generation                                                --- *)
(* -------------------------------------------------------------------------- *)

type pp = {
  self: Markdown.text ;
  ident: ident -> Markdown.text ;
}

(** Quoted string *)
val litteral : string -> Markdown.text

val md_jtype : pp -> jtype -> Markdown.text
val md_tags : ?title:string -> tagInfo list -> Markdown.table
val md_fields : ?title:string -> pp -> fieldInfo list -> Markdown.table

(* -------------------------------------------------------------------------- *)
