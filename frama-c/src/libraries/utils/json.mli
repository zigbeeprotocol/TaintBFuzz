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

(** Json Library

    Remarks:
    - UTF-8 escaping is not supported;
    - Parsers are less {i strict} than Json format;
    - Printers are supposed to {i strictly} conforms to Json format;
    - [Number] can be used to encode non OCaml-primitive numbers,
       for instance Zarith.
*)

(** Json Objects

    Same type than [Yojson.Basic.json]
*)
type json =
  [ `Assoc of (string * json) list
  | `Bool of bool
  | `Float of float
  | `Int of int
  | `List of json list
  | `Null
  | `String of string ]

type t = json

val equal : t -> t -> bool (** Stdlib *)

val compare : t -> t -> int (** Stdlib *)

val pp : Format.formatter -> t -> unit

val pp_dump : Format.formatter -> t -> unit (** without formatting *)

exception Error of Filepath.Normalized.t * int * string
(** file, line, message *)

(** {2 Constructors} *)

val of_bool : bool -> t
val of_int : int -> t
val of_string : string -> t
val of_float : float -> t
val of_list : t list -> t
val of_array : t array -> t
val of_fields : (string * t) list -> t

(** {2 Parsers} *)

(** Parsing raise [Error] in case of error. *)

val load_lexbuf : Lexing.lexbuf -> t
(** Consumes the entire buffer. *)

val load_channel : ?file:string -> in_channel -> t
(** Parses the stream until EOF. *)

val load_string : string -> t
(** Parses the Json in the string. *)

val load_file : string -> t
(** May also raise system exception. *)

(** {2 Printers} *)

(** Printers use formatting unless [~pretty:false]. *)

val save_string : ?pretty:bool -> t -> string
val save_buffer : ?pretty:bool -> Buffer.t -> t -> unit
val save_channel : ?pretty:bool -> out_channel -> t -> unit
val save_formatter : ?pretty:bool -> Format.formatter -> t -> unit
val save_file : ?pretty:bool -> string -> t -> unit

(** {2 Accessors} *)

(** Accessors raise exception [Invalid_argument] in case of wrong format. *)

val bool : t -> bool
(** Extract [True] and [False] only.
    @raise Invalid_argument when the conversion fails. *)

val int : t -> int
(** Convert [Null], [Int], [Float], [Number] and [String] to an [int].
    Floats are truncated with [int_of_float] and [Null] to 0.
    @raise Invalid_argument when the conversion fails. *)

val string : t -> string
(** Convert [Null], [Int], [Float], [Number] and [String] to a [string].
    Floats are truncated with [string_of_float] and [Null] to [""].
    @raise Invalid_argument when the conversion fails. *)

val float : t -> float
(** Convert [Null], [Int], [Float], [Number] and [String] to [float] and [Null] to [0.0].
    @raise Invalid_argument when the conversion fails. *)

val array : t -> t array
(** Extract the array of an [Array] object.
    [Null] is considered an empty array.
    @raise Invalid_argument if the object is not an array. *)

val list : t -> t list
(** Extract the list of an [Array] object.
    [Null] is considered an empty list.
    @raise Invalid_argument if the object is not a list. *)

val assoc : t -> (string * t) list
(** Extract the list of an [Assoc] object.
    [Null] is considered an empty assoc.
    @raise Invalid_argument if the object is not a list. *)

val fold : (string -> t -> 'a -> 'a) -> t -> 'a -> 'a
(** Fold over all fields of the object.
    [Null] is considered an empty object.
    Typical usage is [fold M.add t M.empty] where [M=Map.Make(String)].
    @raise Invalid_argument if the object is not an [Assoc] or [Null] object. *)

val field : string -> t -> t
(** Lookup a field in an object.
    [Null] is considered an empty object.
    @raise Not_found if the field is absent from the object.
    @raise Invalid_argument if the object is not an [Assoc] or [Null] object. *)

(** The functions below read and write to JSON files asynchronously; they are
    intended to be called at different times during execution.
    To avoid reopening, re-reading and rewriting the same file several times,
    they instead operate as following:
    - Read the file on first use, and store it in memory;
    - Perform merge operations using the in-memory representations;
    - Flush the final form to disk before quitting Frama-C.
      The latter is done via function [json_flush_cache] below, which is setup
      to run with an [at_exit] trigger.

    Note: no other functions should modify the contents of [path]; any
    modifications will be overwritten when the cache is flushed.

    @since 23.0-Vanadium
*)

(** Exception raised by the functions below when incompatible types are
    merged. *)
exception CannotMerge of string

(**
   [merge_object path json_obj] recursively merges the object [json_obj] into the
   JSON file [path]. If [path] does not exist, it is created.
   Merge consists in combining values with the same key, e.g. if [path]
   already contains an object [{"kernel": {"options": ["a"]}}], and
   [json_obj] is [{"kernel": {"options": ["b"]}}], the result will be
   [{"kernel": {"options": ["a", "b"]}}]. Cannot merge heterogeneous
   objects, i.e. in the previous example, if "options" were associated
   with a string in [path], trying to merge an array into it would
   raise [CannotMerge].
   The merged object is updated in the memory cache.

   @raise CannotMerge if the objects have conflicting types for
   the same keys, or if the root JSON element is not an object.
   @since 23.0-Vanadium
*)
val merge_object : Filepath.Normalized.t -> t -> unit

(**
   [merge_list path json_array] merges the array [json_array] into the
   JSON file [path]. See [merge_object] for more details.
   Unlike objects, arrays are merged by simply concatenating their list
   of elements.

   @raise CannotMerge if the root JSON element is not an array.
   @since 23.0-Vanadium
*)
val merge_array : Filepath.Normalized.t -> t -> unit

(**
   [from_file path] opens [path] and stores its JSON object in
   a memory cache, to be used by the other related functions.
   @raise Yojson.Json_error if [path] is a malformed JSON file.
   @since 23.0-Vanadium
*)
val from_file: Filepath.Normalized.t -> t

(**
   Flushes the JSON objects in the cache. Returns the names of the written
   files.

   @since 23.0-Vanadium
*)
val flush_cache : unit -> Filepath.Normalized.t list
