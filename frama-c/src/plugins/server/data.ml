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

open Package
module Js = Yojson.Basic
module Ju = Yojson.Basic.Util

(* -------------------------------------------------------------------------- *)
(* --- Data Encoding                                                      --- *)
(* -------------------------------------------------------------------------- *)

type json = Js.t
let pretty = Js.pretty_print ~std:false

module type S =
sig
  type t
  val jtype : jtype
  val of_json : json -> t
  val to_json : t -> json
end

exception InputError of string

let failure ?json msg =
  let add_json msg =
    let msg = match json with
      | None -> msg
      | Some json ->
        Format.asprintf "@[%s:@ %s@]" msg (Js.pretty_to_string json)
    in
    raise(InputError(msg))
  in
  Pretty_utils.ksfprintf add_json msg

let failure_from_type_error msg json =
  failure ~json "%s" msg

let package = Package.package ~name:"data" ~title:"Informations" ()

(* -------------------------------------------------------------------------- *)
(* --- Declared Type                                                      --- *)
(* -------------------------------------------------------------------------- *)

let derived ~package ~id jtype =
  let module Md = Markdown in
  begin
    declare ~package ~name:(Derived.safe id).name
      ~descr:(Md.plain "Safe decoder for" @ Md.code id.name)
      (D_safe(id,jtype)) ;
    declare ~package ~name:(Derived.loose id).name
      ~descr:(Md.plain "Loose decoder for" @ Md.code id.name)
      (D_loose(id,jtype)) ;
    declare ~package ~name:(Derived.order id).name
      ~descr:(Md.plain "Natural order for" @ Md.code id.name)
      (D_order(id,jtype)) ;
  end

let declare ~package ~name ?descr jtype =
  let id = declare_id ~package ~name ?descr (D_type jtype) in
  derived ~package ~id jtype ; Jdata id

(* -------------------------------------------------------------------------- *)
(* --- Option                                                             --- *)
(* -------------------------------------------------------------------------- *)

module Joption(A : S) : S with type t = A.t option =
struct
  type t = A.t option

  let nullable = try ignore (A.of_json `Null) ; true with _ -> false
  let jtype = Joption (if not nullable then A.jtype else Jtuple [A.jtype])

  let to_json = function
    | None -> `Null
    | Some v -> if nullable then `List [A.to_json v] else A.to_json v

  let of_json = function
    | `Null -> None
    | `List [js] when nullable -> Some (A.of_json js)
    | js -> Some (A.of_json js)

end

(* -------------------------------------------------------------------------- *)
(* --- Tuples                                                             --- *)
(* -------------------------------------------------------------------------- *)

module Jpair(A : S)(B : S) : S with type t = A.t * B.t =
struct
  type t = A.t * B.t
  let jtype = Jtuple [A.jtype;B.jtype]
  let to_json (x,y) = `List [ A.to_json x ; B.to_json y ]
  let of_json = function
    | `List [ ja ; jb ] -> A.of_json ja , B.of_json jb
    | js -> failure ~json:js "Expected list with 2 elements"
end

module Jtriple(A : S)(B : S)(C : S) : S with type t = A.t * B.t * C.t =
struct
  type t = A.t * B.t * C.t
  let jtype = Jtuple [A.jtype;B.jtype;C.jtype]
  let to_json (x,y,z) = `List [ A.to_json x ; B.to_json y ; C.to_json z ]
  let of_json = function
    | `List [ ja ; jb ; jc ] -> A.of_json ja , B.of_json jb , C.of_json jc
    | js -> failure ~json:js "Expected list with 3 elements"
end

(* -------------------------------------------------------------------------- *)
(* --- Lists                                                              --- *)
(* -------------------------------------------------------------------------- *)

module Jlist(A : S) : S with type t = A.t list =
struct
  type t = A.t list
  let jtype = Jlist A.jtype
  let to_json xs = `List (List.map A.to_json xs)
  let of_json js = List.map A.of_json (Ju.to_list js)
end

module Jalist(A : S) : S with type t = A.t list =
struct
  type t = A.t list
  let jtype = Jarray A.jtype
  let to_json xs = `List (List.map A.to_json xs)
  let of_json js = List.map A.of_json (Ju.to_list js)
end

(* -------------------------------------------------------------------------- *)
(* --- Arrays                                                             --- *)
(* -------------------------------------------------------------------------- *)

module Jarray(A : S) : S with type t = A.t array =
struct
  type t = A.t array
  let jtype = Jarray A.jtype
  let to_json xs = `List (List.map A.to_json (Array.to_list xs))
  let of_json js = Array.of_list @@ List.map A.of_json (Ju.to_list js)
end

(* -------------------------------------------------------------------------- *)
(* --- Atomic Types                                                       --- *)
(* -------------------------------------------------------------------------- *)

module Junit : S with type t = unit =
struct
  type t = unit
  let jtype = Jnull
  let of_json _js = ()
  let to_json () = `Null
end

module Jany : S with type t = json =
struct
  type t = json
  let jtype = Jany
  let of_json js = js
  let to_json js = js
end

module Jbool : S with type t = bool =
struct
  type t = bool
  let jtype = Jboolean
  let of_json = Ju.to_bool
  let to_json b = `Bool b
end

module Jint : S with type t = int =
struct
  type t = int
  let jtype = Jnumber
  let of_json = Ju.to_int
  let to_json n = `Int n
end

module Jfloat : S with type t = float =
struct
  type t = float
  let jtype = Jnumber
  let of_json = Ju.to_number
  let to_json v = `Float v
end

module Jstring : S with type t = string =
struct
  type t = string
  let jtype = Jstring
  let of_json = Ju.to_string
  let to_json s = `String s
end

module Jalpha : S with type t = string =
struct
  type t = string
  let jtype = Jalpha
  let of_json = Ju.to_string
  let to_json s = `String s
end

(* -------------------------------------------------------------------------- *)
(* --- Text Datatypes                                                     --- *)
(* -------------------------------------------------------------------------- *)

module Jmarkdown : S with type t = Markdown.text =
struct
  type t = Markdown.text
  let jtype =
    let descr = Markdown.plain "Markdown (inlined) text." in
    declare ~package ~name:"markdown" ~descr Jstring
  let of_json js = Markdown.plain (Ju.to_string js)
  let to_json txt = `String (Pretty_utils.to_string Markdown.pp_text txt)
end

module Jtext =
struct
  include Jany
  let jtype =
    let descr = Markdown.plain
        "Rich text format uses `[tag; …text ]` to apply \
         the tag `tag` to the enclosed text. \
         Empty tag `\"\"` can also used to simply group text together." in
    let jdef = Junion [ Jnull; Jstring; Jlist Jself ] in
    declare ~package ~name:"text" ~descr jdef
end

let jpretty = Jbuffer.to_json

(* -------------------------------------------------------------------------- *)
(* --- Functional API                                                     --- *)
(* -------------------------------------------------------------------------- *)

type 'a data = (module S with type t = 'a)

let junit : unit data = (module Junit)
let jany : json data = (module Jany)
let jbool : bool data = (module Jbool)
let jint : int data = (module Jint)
let jfloat : float data = (module Jfloat)
let jstring : string data = (module Jstring)
let jalpha : string data = (module Jalpha)

let jkey ~kind =
  let module JkeyKind =
  struct
    include Jstring
    let jtype = Jkey kind
  end in
  (module JkeyKind : S with type t = string)

let jindex ~kind =
  let module JindexKind =
  struct
    include Jint
    let jtype = Jindex kind
  end in
  (module JindexKind : S with type t = int)

let joption (type a) (d : a data) : a option data =
  let module A = Joption(val d) in
  (module A : S with type t = a option)

let jlist (type a) (d : a data) : a list data =
  let module A = Jlist(val d) in
  (module A : S with type t = a list)

let jalist (type a) (d : a data) : a list data =
  let module A = Jalist(val d) in
  (module A : S with type t = a list)

let jarray (type a) (d : a data) : a array data =
  let module A = Jarray(val d) in
  (module A : S with type t = a array)

(* -------------------------------------------------------------------------- *)
(* --- Records                                                            --- *)
(* -------------------------------------------------------------------------- *)

module Fmap = Map.Make(String)

module Record =
struct

  type 'a record = json Fmap.t

  type ('r,'a) field = {
    member : 'r record -> bool ;
    getter : 'r record -> 'a ;
    setter : 'r record -> 'a -> 'r record ;
  }

  type 'a signature = {
    mutable fields : fieldInfo list ;
    mutable default : 'a record ;
    mutable published : bool ;
  }

  module type S =
  sig
    type r
    include S with type t = r record
    val default : t
    val has : (r,'a) field -> t -> bool
    val get : (r,'a) field -> t -> 'a
    val set : (r,'a) field -> 'a -> t -> t
  end

  let signature () = {
    published = false ;
    fields = [] ;
    default = Fmap.empty ;
  }

  let not_published s =
    if s.published then
      raise (Invalid_argument "Server.Data.Record: already published")

  let check_field_name s name =
    begin
      if List.exists (fun f -> f.Package.fd_name = name) s.fields then
        (let msg = Printf.sprintf "Server.Data.Record: duplicate field %S" name
         in raise (Invalid_argument msg));
      if not (Str.string_match (Str.regexp "[a-zA-Z0-9 _-]+$") name 0) then
        (let msg = Printf.sprintf
             "Server.Data.Record: invalid characters for field %S" name in
         raise (Invalid_argument msg));
    end

  let field (type a r) (s : r signature)
      ~name ~descr ?default (d : a data) : (r,a) field =
    not_published s ;
    check_field_name s name ;
    let module D = (val d) in
    begin match default with
      | None -> ()
      | Some v -> s.default <- Fmap.add name (D.to_json v) s.default
    end ;
    let field = Package.{
        fd_name = name ;
        fd_type = D.jtype ;
        fd_descr = descr ;
      } in
    s.fields <- field :: s.fields ;
    let member r = Fmap.mem name r in
    let getter r = D.of_json (Fmap.find name r) in
    let setter r v = Fmap.add name (D.to_json v) r in
    { member ; getter ; setter }

  let option (type a r) (s : r signature)
      ~name ~descr (d : a data) : (r,a option) field =
    not_published s ;
    check_field_name s name ;
    let module D = (val d) in
    let field = Package.{
        fd_name = name ;
        fd_type = Joption D.jtype ;
        fd_descr = descr ;
      } in
    s.fields <- field :: s.fields ;
    let member r = Fmap.mem name r in
    let getter r =
      try Some (D.of_json (Fmap.find name r)) with Not_found -> None in
    let setter r = function
      | None -> Fmap.remove name r
      | Some v -> Fmap.add name (D.to_json v) r in
    { member ; getter ; setter }

  let publish (type r) ~package ~name ?(descr=[]) (s : r signature) =
    not_published s ;
    let module M =
    struct
      type nonrec r = r
      type t = r record
      let jtype =
        let fields = List.rev s.fields in
        let id = Package.declare_id ~package ~name ~descr (D_record fields) in
        derived ~package ~id (Jrecord (List.map Package.field fields)) ;
        Jdata id
      let default = s.default
      let has fd r = fd.member r
      let get fd r = fd.getter r
      let set fd v r = fd.setter r v
      let of_json js =
        List.fold_left
          (fun r (fd,js) -> Fmap.add fd js r)
          default (Ju.to_assoc js)
      let to_json r : json =
        `Assoc (Fmap.fold (fun fd js fds -> (fd,js) :: fds) r [])
    end in
    begin
      s.default <- Fmap.empty ;
      s.fields <- [] ;
      s.published <- true ;
      (module M : S with type r = r)
    end

end

(* -------------------------------------------------------------------------- *)
(* --- Enums                                                              --- *)
(* -------------------------------------------------------------------------- *)

module Tag =
struct
  type t = Package.tagInfo

  let jtype = declare ~package ~name:"tag"
      ~descr:(Markdown.plain "Enum Tag Description")
      (Jrecord [
          "name",Jalpha ;
          "label",Jmarkdown.jtype ;
          "descr",Jmarkdown.jtype ;
        ])

  let to_json tg = `Assoc Package.[
      "name", `String tg.tg_name ;
      "label", Jmarkdown.to_json tg.tg_label ;
      "descr" , Jmarkdown.to_json tg.tg_descr ;
    ]

  let of_json js = Package.{
      tg_name = Ju.member "name" js |> Ju.to_string ;
      tg_label = Ju.member "label" js |> Jmarkdown.of_json ;
      tg_descr = Ju.member "descr" js |> Jmarkdown.of_json ;
    }

end

module Enum =
struct

  type 'a dictionary = {
    values : (string,'a option) Hashtbl.t ;
    vindex : ('a,string) Hashtbl.t ;
    mutable published : (package * string) option ;
    mutable tags : tagInfo list ;
    mutable prefix : tagInfo list ;
    mutable lookup : ('a -> string) option ;
  }

  type 'a tag = string
  type 'a prefix = 'a dictionary * string

  let tag_name tg = tg
  let tag_label a = function
    | None -> Markdown.plain (String.(capitalize_ascii (lowercase_ascii a)))
    | Some lbl -> lbl

  let dictionary () = {
    published = None ;
    values = Hashtbl.create 0 ;
    vindex = Hashtbl.create 0 ;
    prefix = [] ;
    tags = [] ;
    lookup = None ;
  }

  let tag ~name ?label ~descr ?value (d : 'a dictionary) : 'a tag =
    if Hashtbl.mem d.values name then
      ( let msg = Printf.sprintf "Server.Data.Enum: duplicate tag %S" name in
        raise (Invalid_argument msg) );
    let tg = Package.{
        tg_name = name ;
        tg_label = tag_label name label ;
        tg_descr = descr ;
      } in
    d.tags <- tg :: d.tags ;
    Hashtbl.add d.values name value ;
    begin match value with
      | None -> ()
      | Some v -> Hashtbl.add d.vindex v name
    end ; name

  let add ~name ?label ~descr ?value (d : 'a dictionary) : unit =
    ignore (tag ~name ?label ~descr ?value d)

  let find (d : 'a dictionary) (tg : 'a tag) : 'a =
    match Hashtbl.find d.values tg with
    | Some v -> v
    | None -> raise Not_found

  let find_tag (d : 'a dictionary) name : 'a tag =
    if Hashtbl.mem d.values name then name else
      raise Not_found

  let lookup_index lookup vindex v =
    match lookup with
    | None -> Hashtbl.find vindex v
    | Some f -> try f v with Not_found -> Hashtbl.find vindex v

  let lookup (d : 'a dictionary) (v: 'a) :  'a tag =
    lookup_index d.lookup d.vindex v

  let set_lookup (d : 'a dictionary) (tag : 'a -> 'a tag) =
    d.lookup <- Some tag

  let instance_name = Printf.sprintf "%s_%s"

  let instance (_,prefix) = instance_name prefix

  let prefix ~name ?(var="*") ?label ~descr (d : 'a dictionary) =
    let tg = Package.{
        tg_name = instance_name name var ;
        tg_label = tag_label (name ^ ".") label ;
        tg_descr = descr ;
      } in
    d.prefix <- tg :: d.prefix ; d , name

  let extends ~name ?label ~descr ?value ((d,prefix) : 'a prefix) : 'a tag =
    let name = tag ~name:(instance_name prefix name) ?label ~descr ?value d in
    ( match d.published with
      | None -> ()
      | Some (package,name) ->
        Package.update ~package ~name (D_enum (List.rev d.tags))
    ) ; name

  let to_json name lookup vindex v =
    `String begin
      try lookup_index lookup vindex v
      with Not_found ->
        failure "[%s] Value not found" name
    end

  let of_json name values js =
    let tag = Ju.to_string js in
    match Hashtbl.find values tag with
    | Some v -> v
    | None ->
      failure "[%s] No registered value for tag '%s" name tag
    | exception Not_found ->
      failure "[%s] Not registered tag '%s" name tag

  let tags d = List.rev d.tags

  let publish (type a) ~package ~name ~descr (d : a dictionary) =
    ( match d.published with
      | None -> ()
      | Some _ ->
        let msg = "Server.Data.Enums: already published" in
        raise (Invalid_argument msg) );
    let module M =
    struct
      type t = a
      let jtype =
        let enums = D_enum (List.rev d.tags) in
        let id = Package.declare_id ~package ~name ~descr enums in
        derived ~package ~id (Jenum id) ; Jdata id
      let of_json = of_json name d.values
      let to_json = to_json name d.lookup d.vindex
    end in
    begin
      d.published <- Some (package,name) ;
      (module M : S with type t = a)
    end

end

(* -------------------------------------------------------------------------- *)
(* --- Index                                                              --- *)
(* -------------------------------------------------------------------------- *)

module type Info =
sig
  val name: string
end

(** Simplified [Map.S] *)
module type Map =
sig
  type 'a t
  type key
  val empty : 'a t
  val add : key -> 'a -> 'a t -> 'a t
  val find : key -> 'a t -> 'a
end

module type Index =
sig
  include S
  val get : t -> int
  val find : int -> t
  val clear : unit -> unit
end

module INDEXER(M : Map)(I : Info) :
sig
  type index
  val create : unit -> index
  val clear : index -> unit
  val get : index -> M.key -> int
  val find : index -> int -> M.key
  val to_json : index -> M.key -> json
  val of_json : index -> json -> M.key
end =
struct

  type index = {
    mutable kid : int ;
    mutable index : int M.t ;
    lookup : (int,M.key) Hashtbl.t ;
  }

  let create () = {
    kid = 0 ;
    index = M.empty ;
    lookup = Hashtbl.create 0 ;
  }

  let clear m =
    begin
      m.kid <- 0 ;
      m.index <- M.empty ;
      Hashtbl.clear m.lookup ;
    end

  let get m a =
    try M.find a m.index
    with Not_found ->
      let id = succ m.kid in
      m.kid <- id ;
      m.index <- M.add a id m.index ;
      Hashtbl.add m.lookup id a ; id

  let find m id = Hashtbl.find m.lookup id

  let to_json m a = `Int (get m a)
  let of_json m js =
    let id = Ju.to_int js in
    try find m id
    with Not_found ->
      failure "[%s] No registered id #%d" I.name id

end

module Static(M : Map)(I : Info)
  : Index with type t = M.key =
struct
  module INDEX = INDEXER(M)(I)
  let index = INDEX.create ()
  let clear () = INDEX.clear index
  let get = INDEX.get index
  let find = INDEX.find index
  include
    (struct
      type t = M.key
      let jtype = Jindex I.name
      let of_json = INDEX.of_json index
      let to_json = INDEX.to_json index
    end)
end

module Index(M : Map)(I : Info)
  : Index with type t = M.key =
struct
  module INDEX = INDEXER(M)(I)
  module TYPE : Datatype.S with type t = INDEX.index =
    Datatype.Make
      (struct
        type t = INDEX.index
        include Datatype.Undefined
        let reprs = [INDEX.create()]
        let name = "Server.Data.Index.Type." ^ I.name
        let mem_project = Datatype.never_any_project
      end)
  module STATE = State_builder.Ref(TYPE)
      (struct
        let name = "Server.Data.Index.State." ^ I.name
        let dependencies = []
        let default = INDEX.create
      end)

  let index () = STATE.get ()
  let clear () = INDEX.clear (index())

  let get a = INDEX.get (index()) a
  let find id = INDEX.find (index()) id

  include
    (struct
      type t = M.key
      let jtype = Jindex I.name
      let of_json js = INDEX.of_json (index()) js
      let to_json v = INDEX.to_json (index()) v
    end)

end

module type IdentifiedType =
sig
  type t
  val id : t -> int
end

module Identified(A : IdentifiedType)(I : Info) : Index with type t = A.t =
struct

  type index = (int,A.t) Hashtbl.t

  module TYPE : Datatype.S with type t = index =
    Datatype.Make
      (struct
        type t = index
        include Datatype.Undefined
        let reprs = [Hashtbl.create 0]
        let name = "Server.Data.Identified.Type." ^ I.name
        let mem_project = Datatype.never_any_project
      end)

  module STATE = State_builder.Ref(TYPE)
      (struct
        let name = "Server.Data.Identified.State." ^ I.name
        let dependencies = []
        let default () = Hashtbl.create 0
      end)

  let lookup () = STATE.get ()
  let clear () = Hashtbl.clear (lookup())

  let get = A.id
  let find id = Hashtbl.find (lookup()) id

  include
    (struct
      type t = A.t
      let jtype = Jindex I.name
      let to_json a = `Int (get a)
      let of_json js =
        let k = Ju.to_int js in
        try find k
        with Not_found -> failure "[%s] No registered id #%d" I.name k
    end)

end

(* -------------------------------------------------------------------------- *)
