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

(** ACSL extensions registration module
    @since 21.0-Scandium
*)

open Cil_types
open Logic_typing
open Logic_ptree

(** Untyped ACSL extensions transformers *)
type extension_preprocessor =
  lexpr list -> lexpr list

(** Transformers from untyped to typed ACSL extension *)
type extension_typer =
  typing_context -> location -> lexpr list -> acsl_extension_kind

(** Visitor functions for ACSL extensions *)
type extension_visitor =
  Cil.cilVisitor -> acsl_extension_kind -> acsl_extension_kind Cil.visitAction

type extension_preprocessor_block =
  string * extended_decl list -> string * extended_decl list

type extension_typer_block =
  typing_context -> location -> string * extended_decl list -> acsl_extension_kind

(** Pretty printers for ACSL extensions *)
type extension_printer =
  Printer_api.extensible_printer_type -> Format.formatter ->
  acsl_extension_kind -> unit


(** [register_behavior name ~preprocessor typer ~visitor ~printer ~short_printer status]
    registers new ACSL extension to be used in function contracts with name
    [name].

    The optional [preprocessor] is a function to be applied by the parser on the
    untyped content of the extension before parsing the rest of the processed
    file. By default, this function is the identity.

    The [typer] is applied when transforming the untyped AST to Cil. It recieves
    the typing context of the annotation that can be used to type the received
    logic expressions (see [Logic_typing.typing_context]), and the location of
    the annotation.

    The optional [visitor] allows changing the way the ACSL extension is visited.
    By default, the behavior is [Cil.DoChildren], which ends up visiting
    each identified predicate/term in the list and leave the id as is.

    The optional [printer] allows changing the way the ACSL extension is pretty
    printed. By default, it prints the name of the extension followed by the
    formatted predicates, terms or identifier according to the
    [Cil_types.acsl_extension_kind].

    The optional [short_printer] allows changing the [Printer.pp_short_extended]
    behavior for the ACSL extension. By default, it just prints the [name]. It
    is for example used for the filetree in the GUI.

    The [status] indicates whether the extension can be assigned a property
    status or not.

    Here is a basic example:
    [
    let count = ref 0
    let foo_typer typing_context loc = function
      | p :: [] ->
        Ext_preds
        [ (typing_context.type_predicate
             typing_context
             (typing_context.post_state [Normal])
             p)])
      | [] -> let id = !count in incr count; Ext_id id
      | _ -> typing_context.error loc "expecting a predicate after keyword FOO"
    let () = Acsl_extension.register_behavior "FOO" foo_typer false
    ]
    @plugin development guide
*)
val register_behavior:
  string -> ?preprocessor:extension_preprocessor -> extension_typer ->
  ?visitor:extension_visitor ->
  ?printer:extension_printer -> ?short_printer:extension_printer -> bool ->
  unit

(** Registers extension for global annotation. See [register_behavior].

    @plugin development guide
*)
val register_global:
  string -> ?preprocessor:extension_preprocessor -> extension_typer ->
  ?visitor:extension_visitor ->
  ?printer:extension_printer -> ?short_printer:extension_printer -> bool ->
  unit

(** Registers extension for global block annotation. See [register_behavior].

    @plugin development guide
*)
val register_global_block:
  string -> ?preprocessor:extension_preprocessor_block -> extension_typer_block ->
  ?visitor:extension_visitor ->
  ?printer:extension_printer -> ?short_printer:extension_printer -> bool ->
  unit

(** Registers extension for code annotation to be evaluated at _current_
    program point. See [register_behavior].

    @plugin development guide
*)
val register_code_annot:
  string -> ?preprocessor:extension_preprocessor -> extension_typer ->
  ?visitor:extension_visitor ->
  ?printer:extension_printer -> ?short_printer:extension_printer -> bool ->
  unit

(** Registers extension for code annotation to be evaluated for the _next_
    statement. See [register_behavior].

    @plugin development guide
*)
val register_code_annot_next_stmt:
  string -> ?preprocessor:extension_preprocessor -> extension_typer ->
  ?visitor:extension_visitor ->
  ?printer:extension_printer -> ?short_printer:extension_printer -> bool ->
  unit

(** Registers extension for loop annotation. See [register_behavior].

    @plugin development guide
*)
val register_code_annot_next_loop:
  string -> ?preprocessor:extension_preprocessor -> extension_typer ->
  ?visitor:extension_visitor ->
  ?printer:extension_printer -> ?short_printer:extension_printer -> bool ->
  unit

(** Registers extension both for code and loop annotations.
    See [register_behavior].

    @plugin development guide
*)
val register_code_annot_next_both:
  string -> ?preprocessor:extension_preprocessor -> extension_typer ->
  ?visitor:extension_visitor ->
  ?printer:extension_printer -> ?short_printer:extension_printer -> bool ->
  unit
