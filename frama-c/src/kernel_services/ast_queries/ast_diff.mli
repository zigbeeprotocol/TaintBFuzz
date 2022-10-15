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

(** Compute diff information from an existing project.

    @since 25.0-Manganese
*)

open Cil_types

(** the original project from which a diff is computed. *)
module Orig_project: State_builder.Option_ref with type data = Project.t

(** possible correspondances between new items and original ones. *)
type 'a correspondance =
  [ `Same of 'a (** symbol with identical definition has been found. *)
  | `Not_present (** no correspondance *)
  ]

(** for kernel function, we are a bit more precise than a yes/no answer.
    More precisely, we check whether a function has the same spec,
    the same body, and whether its callees have changed (provided
    the body itself is identical, otherwise, there's no point in checking
    the callees.
*)
type partial_correspondance =
  [ `Spec_changed (** body and callees haven't changed *)
  | `Body_changed (** spec hasn't changed *)
  | `Callees_changed (** spec and body haven't changed *)
  | `Callees_spec_changed (** body hasn't changed *)
  ]

type 'a code_correspondance =
  [ 'a correspondance
  | `Partial of 'a * partial_correspondance
  ]

module type Correspondance_table = sig
  include State_builder.Hashtbl
  val pretty_data: Format.formatter -> data -> unit
end

(** varinfos correspondances *)
module Varinfo:
  Correspondance_table
  with type key = varinfo and type data = varinfo correspondance

module Compinfo:
  Correspondance_table
  with type key = compinfo and type data = compinfo correspondance

module Enuminfo:
  Correspondance_table
  with type key = enuminfo and type data = enuminfo correspondance

module Enumitem:
  Correspondance_table
  with type key = enumitem and type data = enumitem correspondance

module Typeinfo:
  Correspondance_table
  with type key = typeinfo and type data = typeinfo correspondance

module Stmt:
  Correspondance_table
  with type key = stmt and type data = stmt code_correspondance

module Logic_info:
  Correspondance_table
  with type key = logic_info and type data = logic_info correspondance

module Logic_type_info:
  Correspondance_table
  with type key = logic_type_info and type data = logic_type_info correspondance

module Logic_ctor_info:
  Correspondance_table
  with type key = logic_ctor_info and type data = logic_ctor_info correspondance

module Fieldinfo:
  Correspondance_table
  with type key = fieldinfo and type data = fieldinfo correspondance

module Model_info:
  Correspondance_table
  with type key = model_info and type data = model_info correspondance

module Logic_var:
  Correspondance_table
  with type key = logic_var and type data = logic_var correspondance

module Kernel_function:
  Correspondance_table
  with type key = kernel_function
   and type data = kernel_function code_correspondance

module Fundec:
  Correspondance_table
  with type key = fundec and type data = fundec correspondance

(** performs a comparison of AST between the current and the original
    project, which must have been set beforehand.
*)
val compare_ast: unit-> unit

(** [compare_from_prj prj] sets [prj] as the original project
    and fill the tables. *)
val compare_from_prj: Project.t -> unit
