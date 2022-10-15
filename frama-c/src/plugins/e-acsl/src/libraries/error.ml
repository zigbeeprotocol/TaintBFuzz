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

(** Internal module holding the exception of [Error].

    The module is included into [Make_with_opt] later and should not be used
    directly. However we need to have a separate module for the exception so
    that every exception built by [Make] is the exact same type. *)
module Exn = struct
  exception Typing_error of Options.category option * string
  exception Not_yet of Options.category option * string
  exception Not_memoized of Options.category option
end

module type S = sig
  type 'a result = ('a, exn) Result.t
  include module type of Exn
  val make_untypable: string -> exn
  val make_not_yet: string -> exn
  val make_not_memoized: unit -> exn
  val untypable: string -> 'a
  val not_yet: string -> 'a
  val not_memoized: unit -> 'a
  val print_not_yet: string -> unit
  val handle: ('a -> 'a) -> 'a -> 'a
  val generic_handle: ('a -> 'b) -> 'b -> 'a -> 'b
  val retrieve_preprocessing:
    string ->
    ('a -> 'b result) ->
    'a ->
    (Format.formatter -> 'a -> unit) ->
    'b
  val pp_result:
    (Format.formatter -> 'a -> unit) ->
    Format.formatter ->
    'a result ->
    unit
end

module Make_with_opt(P: sig val phase:Options.category option end): S = struct
  type 'a result = ('a, exn) Result.t
  include Exn

  let make_untypable msg = Typing_error (P.phase, msg)
  let make_not_yet msg = Not_yet (P.phase, msg)
  let make_not_memoized () = Not_memoized P.phase

  let untypable msg = raise (make_untypable msg)
  let not_yet msg = raise (make_not_yet msg)
  let not_memoized () = raise (make_not_memoized ())

  let pp_phase fmt phase =
    match phase with
    | Some phase ->
      if Options.verbose_atleast 2 then
        Format.fprintf fmt "@[@ in phase `%a'@]" Options.pp_category phase
    | None -> ()

  let do_print_not_yet phase msg =
    let msg =
      Format.asprintf
        "@[E-ACSL construct@ `%s'@ is not yet supported%a.@]"
        msg
        pp_phase phase
    in
    Options.warning
      ~once:true ~current:true
      "@[%s@ Ignoring annotation.@]" msg

  let print_not_yet msg =
    do_print_not_yet P.phase msg

  let generic_handle f res x =
    try
      f x
    with
    | Typing_error (phase, s) ->
      let msg =
        Format.asprintf "@[invalid E-ACSL construct@ `%s'%a.@]"
          s
          pp_phase phase
      in
      Options.warning
        ~once:true ~current:true
        "@[%s@ Ignoring annotation.@]" msg;
      res
    | Not_yet (phase, s) ->
      do_print_not_yet phase s;
      res

  let handle f x = generic_handle f x x

  let retrieve_preprocessing analyse_name getter parameter pp =
    try
      match getter parameter with
      | Result.Ok res -> res
      | Result.Error exn -> raise exn
    with Not_memoized phase ->
      Options.fatal
        "@[%s was not performed on construct %a%a@]"
        analyse_name
        pp parameter
        pp_phase phase

  let pp_result pp fmt res =
    match res with
    | Result.Ok a -> Format.fprintf fmt "@[%a@]" pp a
    | Result.Error err -> Format.fprintf fmt "@[%s@]" (Printexc.to_string err)
end

module Make(P: sig val phase:Options.category end): S =
  Make_with_opt(struct let phase = Some P.phase end)

include Make_with_opt(struct let phase = None end)

(*
Local Variables:
compile-command: "make"
End:
*)
