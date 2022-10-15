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
(** Data Encoding. *)

(* -------------------------------------------------------------------------- *)
(** {2 Datatypes}

    This module is responsible for marshaling and demarshaling data to handle
    communications between the server and the client in both directions.

    Each datatype must be equipped with functions to encode and decode values
    to/from JSON format. Moreover, data types shall be also properly documented
    and registered in the generated documentation of the Frama-C server.

    Generally speaking, we will have a module with signature [Data.D] for every
    datatype to be exchanged with the server. For simple values, predefined
    modules are already provided. More complex datatypes can be built with some
    functors, typically for options, lists or arrays.

    Records and enumerated types are typical in JSON formatting, but difficult
    to build from OCaml records and abstract datatypes. For those kinds of data,
    we provide an API based on the following general scheme:
    - First create an empty container with its name, documentation and such;
    - Then add each field or constructor to the container;
    - Finally pack the container, which actually registers its complete
      documentation and returns an OCaml value containing the resulting datatype
      module.

    Hence, in addition to module signature [Data.S] for values, there is also a
    polymorphic type ['a Data.data] for module values carrying a data module with
    type [t = 'a].

    The same mechanism is used throughout modules [States] and [Request] each
    time a JSON record or tag is needed. *)
(* -------------------------------------------------------------------------- *)

open Package

type json = Json.t

val pretty : Format.formatter -> json -> unit

(** Datatype module signature. *)
module type S =
sig
  type t
  val jtype : jtype
  val of_json : json -> t
  val to_json : t -> json
end

(* -------------------------------------------------------------------------- *)
(** {2 Atomic Data} *)
(* -------------------------------------------------------------------------- *)

module Junit : S with type t = unit
module Jany : S with type t = json
module Jbool : S with type t = bool
module Jint : S with type t = int
module Jfloat : S with type t = float
module Jstring : S with type t = string
module Jalpha : S with type t = string

(** Rich text encoding, see [Jbuffer]. *)
module Jtext : S with type t = json

module Jmarkdown : S with type t = Markdown.text

(** All-in-one formatter. Return the JSON encoding of formatted text. *)
val jpretty : ?indent:int -> ?margin:int ->
  (Format.formatter -> 'a -> unit) -> 'a -> Jtext.t

(* -------------------------------------------------------------------------- *)
(** {2 Constructors} *)
(* -------------------------------------------------------------------------- *)

module Joption(A : S) : S with type t = A.t option
module Jpair(A : S)(B : S) : S with type t = A.t * B.t
module Jtriple(A : S)(B : S)(C : S) : S with type t = A.t * B.t * C.t
module Jlist(A : S) : S with type t = A.t list
module Jalist(A : S) : S with type t = A.t list
module Jarray(A : S) : S with type t = A.t array

(* -------------------------------------------------------------------------- *)
(** {2 Functional API} *)
(* -------------------------------------------------------------------------- *)

(** Polymorphic data value. *)
type 'a data = (module S with type t = 'a)

val junit : unit data
val jany : json data
val jbool : bool data
val jint : int data
val jfloat : float data
val jstring : string data
val jalpha : string data
val jindex : kind:string -> int data
val jkey : kind:string -> string data
val jlist : 'a data -> 'a list data
val jalist : 'a data -> 'a list data
val jarray : 'a data -> 'a array data
val joption : 'a data -> 'a option data

(**
   Declare the derived names for the provided type.
   Shall not be used directely.
*)
val derived : package:package -> id:ident -> jtype -> unit

(**
   Declare a new type and returns its alias.
   Same as [Jdata (declare_id ~package ~name (D_type js))].
   Automatically declare the derived names.
*)
val declare :
  package:package ->
  name:string ->
  ?descr:Markdown.text ->
  jtype -> jtype

(* -------------------------------------------------------------------------- *)
(** {2 Records} *)
(* -------------------------------------------------------------------------- *)

(** Record factory.

    You shall start by declaring a (ghost) type [r] and call
    [Record.signature] to create a signature of type [r], which will be
    your container to register your record fields.

    Then, populate the signature with [Record.field] or [Record.option].
    Finally, you shall call [Record.publish] to pack the record signature and
    obtain a new data module of type [Record with type r = r],
    which gives you a [Data] with an opaque
    type [t = r record] with fields of type [(r,a) field].

    {[
      (* ---- Exemple of Record Data --- *)
      type r
      let s = Record.signature () in
      let fd_a = Record.field s ~name:"a" ~descr:"..." (module A) in
      let fd_b = Record.field s ~name:"b" ~descr:"..." (module B) in
      let r = Record.publish s ~page ~kind ~name ~descr
      module M = (val r) : Record with type r = r)

      let make a b = M.default |> M.set fd_a a |> M.set fd_b b
    ]}
*)
module Record :
sig

  (** Records of type ['a]. *)
  type 'a record

  (** Opened signature for record of type ['a]. *)
  type 'a signature

  (** Field of type ['b] for a record of type ['a]. *)
  type ('a,'b) field

  (** Data with [type t = r record].
      Also contains getters and setters for fields. *)
  module type S =
  sig
    type r
    include S with type t = r record
    val default : t
    val has : (r,'a) field -> t -> bool
    val get : (r,'a) field -> t -> 'a
    val set : (r,'a) field -> 'a -> t -> t
  end

  (** Create a new, opened record type. *)
  val signature : unit -> 'a signature

  (** Adds a field to an opened record. *)
  val field : 'r signature ->
    name:string -> descr:Markdown.text -> ?default:'a -> 'a data ->
    ('r,'a) field

  (** Adds a optional field to an opened record. *)
  val option : 'r signature ->
    name:string -> descr:Markdown.text -> 'a data ->
    ('r,'a option) field

  (** Publish and close an opened record. *)
  val publish : package:package -> name:string -> ?descr:Markdown.text ->
    'a signature -> (module S with type r = 'a)

end

(* -------------------------------------------------------------------------- *)
(** {2 Enums} *)
(* -------------------------------------------------------------------------- *)

module Tag : S with type t = tagInfo

(** Enum factory.

    You shall start by declaring a dictionary with [Enum.dictionary] for your
    values. Then, populate the dictionary with [Enum.tag] values. Finally, you
    shall call [Enum.publish] to obtain a new data module for your type.

    You have two options for computing tags: either you provide values when
    declaring tags, and these tags will be associated to registered values for
    both directions; alternatively you might provide a [~tag] function to
    [Enum.publish].

    The difficulty when providing values only at tag definition is to ensure
    that all possible value has been registered.

    The conversion values from and to json may fail when no value has been
    registered with tags. *)
module Enum :
sig

  type 'a dictionary
  type 'a tag
  type 'a prefix

  val tag_name : 'a tag -> string

  (** Creates an opened, empty dictionary. *)
  val dictionary : unit -> 'a dictionary

  (** Register a new tag in the dictionary.
      The default label is the capitalized name.
      The provided value, if any, will be used for decoding json tags.
      If would be used also for encoding values to json tags if no [~tag]
      function is provided when publishing the dictionary.
      Registered values must be hashable with [Hashtbl.hash] function.

      You may register a new tag {i after} the dictionary has been published. *)
  val tag :
    name:string ->
    ?label:Markdown.text -> descr:Markdown.text ->
    ?value:'a ->
    'a dictionary -> 'a tag

  (** Same as [tag] but to not return the associated tag. *)
  val add :
    name:string ->
    ?label:Markdown.text -> descr:Markdown.text ->
    ?value:'a ->
    'a dictionary -> unit

  (** Returns the value associated to some tag.
      @raise Not_found if no value is associated to the tag. *)
  val find: 'a dictionary -> 'a tag -> 'a

  (** Returns the tag associated to a value.
      @raise Not_found if no value is associated to the tag. *)
  val lookup: 'a dictionary -> 'a -> 'a tag

  (** Returns the tag from its name.
      @raise Not_found if no tag has been registered with this name. *)
  val find_tag: 'a dictionary -> string -> 'a tag

  (** Register a new prefix tag in the dictionary.
      The default label is the capitalized prefix.
      To decoding from json is provided to prefix tags.
      Encoding is done by emitting tags with form ['prefix:*'].
      The variable part of the prefix is documented as ['prefix:xxx']
      when [~var:"xxx"] is provided.

      You may register a new prefix-tag {i after} the dictionary has
      been published. *)
  val prefix :
    name:string -> ?var:string ->
    ?label:Markdown.text -> descr:Markdown.text ->
    'a dictionary -> 'a prefix

  (** Returns the tag for a value associated with the given prefix. *)
  val instance : 'a prefix -> string -> 'a tag

  (** Publish a new instance in the documentation. *)
  val extends :
    name:string ->
    ?label:Markdown.text -> descr:Markdown.text ->
    ?value:'a ->
    'a prefix -> 'a tag

  (** Obtain all the tags registered in the dictionary so far. *)
  val tags : 'a dictionary -> Tag.t list

  (** Set tagging function for values. If the lookup function
      raises `Not_found`, the dictionary will use the tag associated
      with the provided value, if any. *)
  val set_lookup : 'a dictionary -> ('a -> 'a tag) -> unit

  (**
     Publish the dictionary. No more tag nor prefix can be added afterwards.
     If no [~tag] function is provided, the values registered with tags are used.
  *)
  val publish : package:package -> name:string -> descr:Markdown.text ->
    'a dictionary -> (module S with type t = 'a)

end

(* -------------------------------------------------------------------------- *)
(** {2 Indexed Values}

    These datatypes automatically index complex values with
    unique identifiers. This avoids to encode the internal OCaml
    representation of each value, by only providing to the server
    a unique identifier for each value.

    These datatype functors come into three flavors:
    - [Index()] for projectified datatypes,
    - [Static()] for project independant datatypes,
    - [Identified()] for projectified values already identified by integers.

*)
(* -------------------------------------------------------------------------- *)

(** Datatype information. *)
module type Info =
sig
  val name: string
end

(** Simplified [Map.S]. *)
module type Map =
sig
  type 'a t
  type key
  val empty : 'a t
  val add : key -> 'a -> 'a t -> 'a t
  val find : key -> 'a t -> 'a
end

(** Datatype extended with access to value identifiers. *)
module type Index =
sig
  include S
  val get : t -> int
  val find : int -> t
  (** @raise Not_found if not registered. *)

  val clear : unit -> unit
  (** Clear index tables. Use with extreme care. *)
end

(** Builds an indexer that {i does not} depend on current project. *)
module Static(M : Map)(I : Info) : Index with type t = M.key

(** Builds a {i projectified} index. *)
module Index(M : Map)(I : Info) : Index with type t = M.key

(** Datatype already identified by unique integers. *)
module type IdentifiedType =
sig
  type t
  val id : t -> int
end

(** Builds a {i projectified} index on types with {i unique} identifiers. *)
module Identified(A : IdentifiedType)(I : Info) : Index with type t = A.t

(* -------------------------------------------------------------------------- *)
(** {2 Error handling}

    These utilities shall be used when writing your own encoding and decoding
    values to JSON format.
*)
(* -------------------------------------------------------------------------- *)

(** Exception thrown during the decoding of a request's inputs. *)
exception InputError of string

val failure : ?json:json -> ('a, Format.formatter, unit, 'b) format4 -> 'a
(** @raise InputError with provided message. *)

val failure_from_type_error : string -> json -> 'a
(** @raise InputError from [Yojson.Basic.Util.Type_error] arguments. *)

(* -------------------------------------------------------------------------- *)
