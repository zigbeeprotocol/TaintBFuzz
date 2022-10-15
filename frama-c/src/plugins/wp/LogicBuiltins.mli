(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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
(* --- Linker for ACSL Builtins                                           --- *)
(* -------------------------------------------------------------------------- *)

open Cil_types
open Lang

type category = Lang.lfun Qed.Logic.category

type kind =
  | Z                   (** integer *)
  | R                   (** real *)
  | I of Ctypes.c_int   (** C-ints *)
  | F of Ctypes.c_float (** C-floats *)
  | A                   (** Abstract Data *)

val kind_of_tau : tau -> kind

(** Add a new builtin. This builtin will be shared with all created drivers *)
val add_builtin : string -> kind list -> lfun -> unit

type driver
val driver: driver Context.value

val new_driver:
  id:string ->
  ?base:driver ->
  ?descr:string ->
  ?includes:string list ->
  ?configure:(unit -> unit) -> unit ->
  driver
(** Creates a configured driver from an existing one.
    Default:
    - base: builtin WP driver
    - descr: id
    - includes: []
    - configure: No-Op
      The configure is the only operation allowed to modify the content of the
      newly created driver. Except during static initialization of builtin driver.
*)

val id : driver -> string
val descr : driver -> string
val is_default : driver -> bool
val compare : driver -> driver -> int

val find_lib: string -> string
(** find a file in the includes of the current drivers *)

val dependencies : string -> string list
(** Of external theories. Raises Not_found if undefined *)

val add_library : string -> string list -> unit
(** Add a new library or update the dependencies of an existing one *)

val add_alias : source:Filepath.position -> string -> kind list -> alias:string -> unit -> unit

val add_type : ?source:Filepath.position -> string -> library:string ->
  ?link:string -> unit -> unit

val add_ctor : source:Filepath.position -> string -> kind list ->
  library:string -> link:Qed.Engine.link -> unit -> unit

val add_logic : source:Filepath.position -> kind -> string -> kind list ->
  library:string -> ?category:category -> link:Qed.Engine.link ->
  unit -> unit

val add_predicate : source:Filepath.position -> string -> kind list ->
  library:string -> link:string ->
  unit -> unit

val add_option :
  driver_dir:string -> string -> string -> library:string -> string -> unit
(** add a value to an option (group, name) *)

val set_option :
  driver_dir:string -> string -> string -> library:string -> string -> unit
(** reset and add a value to an option (group, name) *)

type doption

type sanitizer = (driver_dir:string -> string -> string)

val create_option: sanitizer:sanitizer -> string -> string -> doption
(** [add_option_sanitizer ~driver_dir group name]
    add a sanitizer for group [group] and option [name] *)

val get_option : doption -> library:string -> string list
(** return the values of option (group, name),
    return the empty list if not set *)

type builtin =
  | ACSLDEF
  | LFUN of lfun
  | HACK of (F.term list  -> F.term)

val logic : logic_info -> builtin
val ctor : logic_ctor_info -> builtin
val constant : string -> builtin
val lookup : string -> kind list -> builtin

(** Replace a logic definition or predicate by a built-in function.
    The LogicSemantics compilers will replace `Pcall` and `Tcall` instances
    of this symbol with the provided Qed function on terms. *)
val hack : string -> (F.term list -> F.term) -> unit

(** Replace a logic type definition or predicate by a built-in type. *)
val hack_type : string -> (F.tau list -> F.tau) -> unit

val dump : unit -> unit
