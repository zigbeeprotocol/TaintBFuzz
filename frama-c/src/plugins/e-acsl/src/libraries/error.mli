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

(** Handling errors. *)

module type S = sig
  type 'a result = ('a, exn) Result.t
  (** Represent either a result of type ['a] or an error with an exception. *)

  exception Typing_error of Options.category option * string
  (** Typing error where the first element is the phase where the error occured
      and the second element is the error message. *)

  exception Not_yet of Options.category option * string
  (** "Not yet supported" error where the first element is the phase where the
      error occured and the second element is the error message. *)

  exception Not_memoized of Options.category option
  (** "Not memoized" error with the phase where the error occured. *)

  val make_untypable: string -> exn
  (** Make a [Typing_error] exception with the given message. *)

  val make_not_yet: string -> exn
  (** Make a [Not_yet] exception with the given message. *)

  val make_not_memoized: unit -> exn
  (** Make a [Not_memoized] exception with the given message. *)

  val untypable: string -> 'a
  (** @raise Typing_error with the given message for the current phase. *)

  val not_yet: string -> 'a
  (** @raise Not_yet with the given message for the current phase. *)

  val not_memoized: unit -> 'a
  (** @raise Not_memoized for the current phase. *)

  val print_not_yet: string -> unit
  (** Print the "not yet supported" message without raising an exception. *)

  val handle: ('a -> 'a) -> 'a -> 'a
  (** Run the closure with the given argument and handle potential errors.
      Return the provide argument in case of errors. *)

  val generic_handle: ('a -> 'b) -> 'b -> 'a -> 'b
  (** Run the closure with the given argument and handle potential errors.
      Return the additional argument in case of errors. *)

  val retrieve_preprocessing:
    string ->
    ('a -> 'b result) ->
    'a ->
    (Format.formatter -> 'a -> unit) ->
    'b
  (** Retrieve the result of a preprocessing phase, which possibly failed.
      The [string] argument and the formatter are used to display a message in
      case the preprocessing phase did not compute the required result. *)

  val pp_result:
    (Format.formatter -> 'a -> unit) ->
    Format.formatter ->
    'a result ->
    unit
    (** [pp_result pp] where [pp] is a formatter for ['a] returns a formatter for
        ['a result]. *)
end

(** Functor to build an [Error] module for a given [phase]. *)
module Make(P: sig val phase:Options.category end): S

(** The [Error] module implements [Error.S] with no phase. *)
include S

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
