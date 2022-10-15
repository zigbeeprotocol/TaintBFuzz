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

(** Internal Cil printer.

    Must not be used by plug-in developers: use module {!Printer} instead.
    In particular, this pretty-printer is incorrect regarding annotations.
    It should only be used by modules linked before {!Annotations}.

    @since Fluorine-20130401 *)

include Printer_api.S

(** ["assert"], ["check"] or ["admit"]. *)
val string_of_assert : Cil_types.predicate_kind -> string

(** ["assertion"], ["check"] or ["admit"]. *)
val name_of_assert : Cil_types.predicate_kind -> string

(** ["lemma"], ["check lemma"] or ["axiom"]. *)
val string_of_lemma : Cil_types.predicate_kind -> string

(** clause, prefixed by ["check"] or ["admit"]. *)
val string_of_predicate : kw:string -> Cil_types.predicate_kind -> string

(** same as [string_of_lemma] with ["_"] for separator. *)
val ident_of_lemma : Cil_types.predicate_kind -> string

(** same as [string_of_predicate] with ["_"] for separator. *)
val ident_of_predicate : kw:string -> Cil_types.predicate_kind -> string

(** pretty prints [string_of_assert]. *)
val pp_assert_kind : Format.formatter -> Cil_types.predicate_kind -> unit

(** pretty prints [string_of_lemma]. *)
val pp_lemma_kind : Format.formatter -> Cil_types.predicate_kind -> unit

(** pretty prints [string_of_predicate]. *)
val pp_predicate_kind :
  kw:string -> Format.formatter -> Cil_types.predicate_kind -> unit

val get_termination_kind_name: Cil_types.termination_kind -> string

val register_shallow_attribute: string -> unit
(** Register an attribute that will never be pretty printed. *)

val state: Printer_api.state

val print_global: Cil_types.global -> bool
(** Is the given global displayed by the pretty-printer.
    @since Aluminium-20160501 *)

(**/**)

val set_extension_handler:
  print:(string -> Printer_api.extensible_printer_type ->
         Format.formatter -> Cil_types.acsl_extension_kind -> unit) ->
  short_print:(string -> Printer_api.extensible_printer_type ->
               Format.formatter -> Cil_types.acsl_extension_kind -> unit) ->
  unit
(** Used to setup a reference related to the handling of ACSL extensions.
    If your name is not [Acsl_extension], do not call this.
    @since 21.0-Scandium
*)

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
