(**************************************************************************)
(*                                                                        *)
(*  This file is part of the Frama-C's E-ACSL plug-in.                    *)
(*                                                                        *)
(*  Copyright (C) 2012-2021                                               *)
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
open Analyses_types

val case_globals :
  default:(unit -> 'a) ->
  ?builtin:(varinfo -> 'a) ->
  ?fc_compiler_builtin:(varinfo -> 'a) ->
  ?rtl_symbol:(global -> 'a) ->
  ?fc_stdlib_generated:(varinfo -> 'a) ->
  ?var_fun_decl:(varinfo -> 'a) ->
  ?var_init:(varinfo -> 'a) ->
  ?var_def:(varinfo -> init -> 'a) ->
  ?glob_annot:(global_annotation -> 'a) ->
  fun_def:(fundec -> 'a) ->
  global -> 'a
(** Function to descend into the root of the ast according to the various cases
    relevant for E-ACSL. Each of the named argument corresponds to the function
    to be applied in the corresponding case. The [default] case is used if any
    optional argument is not given
    - [builtin] is the case for C builtins
    - [fc_builtin_compiler] is the case for frama-c or compiler builtins
    - [rtl_symbol] is the case for any global coming from the runtime library
    - [fc_stdlib_generated] is the case for frama-c or standard library
      generated functions
    - [var_fun_decl] is the case for variables or functions declarations
    - [var_init] is the case for variable definition wihtout an initialization
      value
    - [var_def] is the case for variable definitions with an initialization
      value
    - [glob_annot] is the case for global annotations
    - [fun_def] is the case for function definition. *)

(** Visitor to visit the AST in the same manner than the injector.

    [new visitor cat] creates a visitor with [cat] as the category to use for
    the [Error] module in the visitor.

    For the root of the AST, not the global level, only visit the cases that
    are relevant to E-ACSL. Each case is handled by a method of the visitor. The
    cases are similar, and similarly named as the ones of the function
    [case_globals].

    For the rest of the AST, the kind of the visited annotation is recorded and
    accessed through the method [get_akind]. While visiting annotations
    currently not supported by E-ACSL, the [get_visit_error] returns a [not_yet]
    exception. Any visitor that inherits from [E_acsl_visitor.visitor] can
    decide wether continue its processing or not as it sees fit.

    As a result of the custom visit of the AST, the methods [vcode_annot] and
    [vspec] skip their children, since they are already visited by [vstmt_aux].
    Be sure to use the method [visit] (and associated methods) if you need to
    visit the children of those nodes.

    To support these functionalities, the methods [vglob_aux] and [vstmt_aux]
    have been heavily modified and should not be overriden further. *)
class visitor :
  Options.category ->
  object
    inherit Visitor.frama_c_inplace

    (* Functions for [case_globals] *)
    method private default: unit -> global list Cil.visitAction
    method builtin: varinfo -> global list Cil.visitAction
    method fc_compiler_builtin: varinfo -> global list Cil.visitAction
    method rtl_symbol: global -> global list Cil.visitAction
    method fc_stdlib_generated: varinfo -> global list Cil.visitAction
    method var_fun_decl: varinfo -> global list Cil.visitAction
    method var_init: varinfo -> global list Cil.visitAction
    method var_def: varinfo -> init -> global list Cil.visitAction
    method glob_annot: global_annotation -> global list Cil.visitAction
    method fun_def: fundec -> global list Cil.visitAction

    method get_visit_error: unit -> exn option
    (** @return a potential error during the visit of the AST (for instance a
        [not_yet] error while visiting assigns clause in behaviors). *)

    method get_akind: unit -> annotation_kind
    (** @return The current kind of annotation being visited. *)

    method visit: 'a 'b.
      ?vcode_annot:bool ->
      ?vspec:bool ->
      (Visitor.frama_c_visitor -> 'a -> 'b) ->
      'a ->
      'b
    (** [visit ?vode_annot ?vspec visit_func item] starts a visit of the AST
        from [item] with the Frama-C visit function [visit_func].

        If [vcode_annot] is true, then the method [vcode_annot] will visit its
        children, otherwise they are skipped and will only be visited through
        [vstmt_aux].

        If [vspec] is true, then the method [vspec] will visit its children,
        otherwise they are skipped and will only be visited through
        [vstmt_aux]. *)

    method visit_file: file -> unit
    (** [visit file] starts a visit of the AST from the given [file] node. *)

    method visit_code_annot: code_annotation -> code_annotation
    (** [visit code_annot] starts a visit of the AST from the given [code_annot]
        node. *)

    method visit_predicate: predicate -> predicate
    (** [visit_predicate p] starts a visit of the AST from the given [predicate]
        node. *)
  end


(**************************************************************************)
(********************** Forward references ********************************)
(**************************************************************************)

val must_translate_ppt_ref: (Property.t -> bool) ref

val must_translate_ppt_opt_ref: (Property.t option -> bool) ref

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
