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
(** Ast Data *)
(* -------------------------------------------------------------------------- *)

open Package
open Cil_types

module Position : Data.S with type t = Filepath.position

module Kf : Data.S with type t = kernel_function
module Fundec : Data.S with type t = fundec
module Ki : Data.S with type t = kinstr
module Stmt : Data.S with type t = stmt
module Lval : Data.S with type t = kinstr * lval

module Marker :
sig
  include Data.S with type t = Printer_tag.localizable

  val jstmt : jtype
  val jdecl : jtype
  val jlval : jtype
  val jexpr : jtype
  val jterm : jtype
  val jglobal : jtype
  val jproperty : jtype

  val create : t -> string
  (** Memoized unique identifier. *)

  val lookup : string -> t
  (** Get back the localizable, if any. *)
end

module KfMarker : Data.S with type t = kernel_function * Printer_tag.localizable

(* -------------------------------------------------------------------------- *)
(** Ast Printer *)
(* -------------------------------------------------------------------------- *)

module Printer : Printer_tag.S_pp

(* -------------------------------------------------------------------------- *)
(** Ast Information *)
(* -------------------------------------------------------------------------- *)

module Information :
sig
  (**
     Registers a marker information printer.
     Identifier [id] shall be unique.
     Label [label] shall be very short.
     Description shall succinctly describe the kind of information.
     If the optional [enable] function is provided, the information printer is
     only used when [enable ()] returns true.
     The printer is allowed to raise [Not_found] exception when there is no
     information for the localizable.
  *)
  val register :
    id:string -> label:string -> title:string -> ?enable:(unit -> bool) ->
    (Format.formatter -> Printer_tag.localizable -> unit) -> unit

  (** Updated information signal *)
  val signal : Request.signal

  (** Emits a signal to server clients to reload AST marker information. *)
  val update : unit -> unit
end

(* -------------------------------------------------------------------------- *)
(** Globals *)
(* -------------------------------------------------------------------------- *)

module Functions :
sig
  val array : kernel_function States.array
end

(* -------------------------------------------------------------------------- *)
