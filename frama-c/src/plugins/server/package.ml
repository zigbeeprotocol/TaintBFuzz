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

module Senv = Server_parameters
module Md = Markdown

(* -------------------------------------------------------------------------- *)

type plugin = Kernel | Plugin of string
type ident = { plugin: plugin; package: string list; name: string }

let pp_step fmt a =
  ( Format.pp_print_string fmt a ; Format.pp_print_char fmt '.' )

let pp_plugin fmt = function
  | Kernel -> pp_step fmt "kernel"
  | Plugin p -> pp_step fmt "plugins" ; pp_step fmt p

let pp_ident fmt { plugin ; package ; name } =
  ( pp_plugin fmt plugin ;
    List.iter (pp_step fmt) package ;
    Format.pp_print_string fmt name )

(* -------------------------------------------------------------------------- *)
(* --- Name Resolution                                                    --- *)
(* -------------------------------------------------------------------------- *)

module Std = Stdlib
module Id = struct type t = ident let compare = Std.compare end
module IdMap = Map.Make(Id)
module IdSet = Set.Make(Id)
module NameSet = Set.Make(String)

module Scope =
struct

  let rec inpkg ids = function
    | [] -> ids
    | [p] -> p::ids
    | _::ps -> inpkg ids ps

  let relative ~source ~target ids =
    if target = source then ids else
      match target with
      | Kernel -> ids
      | Plugin p -> p::ids

  let target p ids =
    match p with
    | Kernel -> "kernel" :: ids
    | Plugin p -> "plugins" :: p :: ids

  (* propose various abbreviations ; finally render full qualified name *)
  let ranked source { plugin ; package ; name } k =
    String.concat "_" @@
    let name = [name] in
    match k with
    | 0 -> name
    | 1 -> relative ~source ~target:plugin name
    | 2 -> relative ~source ~target:plugin (inpkg name package)
    | 3 -> relative ~source ~target:plugin (package @ name)
    | _ -> target plugin (package @ name)

  type t = {
    source : plugin ;
    mutable clashes : bool ;
    mutable index : (string,int IdMap.t) Hashtbl.t ;
    mutable names : string IdMap.t ;
    mutable reserved : NameSet.t ;
  }

  let create source = {
    source ;
    index = Hashtbl.create 0 ;
    clashes = false ;
    names = IdMap.empty ;
    reserved = NameSet.empty ;
  }

  let rec non_reserved scope id rk =
    let a = ranked scope.source id rk in
    if NameSet.mem a scope.reserved then
      non_reserved scope id (succ rk)
    else a,rk

  let push scope id rk =
    begin
      let name, rk = non_reserved scope id rk in
      scope.names <- IdMap.add id name scope.names ;
      let index = scope.index in
      match Hashtbl.find_opt index name with
      | None ->
        Hashtbl.add index name (IdMap.add id rk IdMap.empty)
      | Some idks ->
        if IdMap.mem id idks then
          scope.clashes <- true
        else
          Hashtbl.replace index name (IdMap.add id rk idks)
    end

  let use scope id =
    if not (IdMap.mem id scope.names) then
      push scope id 0

  let reserve scope name =
    assert (IdMap.is_empty scope.names) ;
    scope.reserved <- NameSet.add name scope.reserved

  let declare scope id =
    begin
      let { name } = id in
      if NameSet.mem name scope.reserved then
        Senv.fatal "Reserved name for identifier '%a'" pp_ident id ;
      scope.names <- IdMap.add id name scope.names ;
      scope.reserved <- NameSet.add name scope.reserved ;
    end

  let rec resolve scope =
    if not scope.clashes then scope.names else
      begin
        let index = scope.index in
        scope.index <- Hashtbl.create 0 ;
        scope.clashes <- false ;
        Hashtbl.iter
          (fun _name idks ->
             match IdMap.bindings idks with
             | [id,rk] ->
               push scope id rk
             | idks ->
               List.iter (fun (id,rk) -> push scope id (succ rk)) idks
          ) index ;
        resolve scope
      end

end

(* -------------------------------------------------------------------------- *)
(* --- JSON Datatypes                                                     --- *)
(* -------------------------------------------------------------------------- *)

type jtype =
  | Jany
  | Jnull
  | Jboolean
  | Jnumber
  | Jstring
  | Jalpha (* string primarily compared without case *)
  | Jtag of string (* single constant string *)
  | Jkey of string (* kind of a string used for indexing *)
  | Jindex of string (* kind of an integer used for indexing *)
  | Joption of jtype
  | Jdict of jtype (* dictionaries *)
  | Jlist of jtype (* order does not matter *)
  | Jarray of jtype (* order matters *)
  | Jtuple of jtype list
  | Junion of jtype list
  | Jrecord of (string * jtype) list
  | Jdata of ident
  | Jenum of ident (* enum type declaration *)
  | Jself (* for (simply) recursive types *)

(* -------------------------------------------------------------------------- *)
(* --- Declarations                                                       --- *)
(* -------------------------------------------------------------------------- *)

type fieldInfo = {
  fd_name: string;
  fd_type: jtype;
  fd_descr: Markdown.text;
}

type tagInfo = {
  tg_name: string;
  tg_label: Markdown.text;
  tg_descr: Markdown.text;
}

type paramInfo =
  | P_value of jtype
  | P_named of fieldInfo list

type requestInfo = {
  rq_kind: [ `GET | `SET | `EXEC ];
  rq_input: paramInfo ;
  rq_output: paramInfo ;
  rq_signals: string list ;
}

type arrayInfo = {
  arr_key: string;
  arr_kind: jtype;
}

type declKindInfo =
  | D_signal
  | D_type of jtype
  | D_enum of tagInfo list
  | D_record of fieldInfo list
  | D_request of requestInfo
  | D_value of jtype
  | D_state of jtype
  | D_array of arrayInfo (* key kind *)
  | D_safe of ident * jtype (* safe decoder *)
  | D_loose of ident * jtype (* loose decoder *)
  | D_order of ident * jtype (* natural ordering *)

type declInfo = {
  d_ident : ident;
  d_descr : Markdown.text;
  d_kind : declKindInfo;
}

type packageInfo = {
  p_plugin : plugin ;
  p_package : string list ;
  p_title : string ;
  p_descr : Markdown.text ;
  p_readme : string option ;
  p_content : declInfo list ;
}

let name_of_ident ?(sep=".") id =
  String.concat sep @@ match id.plugin with
  | Kernel -> "kernel" :: id.package @ [ id.name ]
  | Plugin p -> "plugins" :: p :: (id.package @ [id.name ])

let name_of_pkg ?(sep=".") plugin package =
  String.concat sep @@ match plugin with
  | Kernel -> "kernel" :: package
  | Plugin p -> "plugins" :: p :: package

let name_of_pkginfo ?sep { p_plugin ; p_package } =
  name_of_pkg ?sep p_plugin p_package

let pp_pkgname fmt { p_plugin ; p_package } =
  ( pp_plugin fmt p_plugin ;
    List.iter (pp_step fmt) p_package )

(* -------------------------------------------------------------------------- *)
(* --- Derived Names                                                      --- *)
(* -------------------------------------------------------------------------- *)

let derived ?prefix ?suffix id =
  let capitalize = String.capitalize_ascii in
  match prefix , suffix with
  | None , None -> id
  | Some p , None -> { id with name = p ^ capitalize id.name }
  | None , Some q -> { id with name = id.name ^ q }
  | Some p , Some q -> { id with name = p ^ capitalize id.name ^ q }

module Derived =
struct
  let signal id = derived ~prefix:"signal" id
  let getter id = derived ~prefix:"get" id
  let setter id = derived ~prefix:"set" id
  let data id = derived ~suffix:"Data" id
  let fetch id = derived ~prefix:"fetch" id
  let reload id = derived ~prefix:"reload" id
  let order id = derived ~prefix:"by" id
  let loose id = derived ~prefix:"j" id
  let safe id = derived ~prefix:"j" ~suffix:"Safe" id
  let decode ~safe:ok id = if ok then safe id else loose id
end

(* -------------------------------------------------------------------------- *)
(* --- Visitors                                                           --- *)
(* -------------------------------------------------------------------------- *)

let rec isRecursive = function
  | Jself -> true
  | Jdata _ | Jenum _
  | Jany | Jnull | Jboolean | Jnumber
  | Jstring | Jalpha | Jkey _ | Jindex _ | Jtag _ -> false
  | Joption js | Jdict js  | Jarray js | Jlist js -> isRecursive js
  | Jtuple js | Junion js -> List.exists isRecursive js
  | Jrecord fjs -> List.exists (fun (_,js) -> isRecursive js) fjs

let rec visit_jtype fn = function
  | Jany | Jself | Jnull | Jboolean | Jnumber
  | Jstring | Jalpha | Jkey _ | Jindex _ | Jtag _ -> ()
  | Joption js | Jdict js  | Jarray js | Jlist js -> visit_jtype fn js
  | Jtuple js | Junion js -> List.iter (visit_jtype fn) js
  | Jrecord fjs -> List.iter (fun (_,js) -> visit_jtype fn js) fjs
  | Jdata id | Jenum id ->
    begin
      fn id ;
      fn (Derived.safe id) ;
      fn (Derived.loose id) ;
      fn (Derived.order id) ;
    end

let visit_field f { fd_type } = visit_jtype f fd_type

let visit_param f = function
  | P_value js -> visit_jtype f js
  | P_named fds -> List.iter (visit_field f) fds

let visit_request f { rq_input ; rq_output } =
  ( visit_param f rq_input ; visit_param f rq_output )

let visit_dkind f = function
  | D_signal | D_enum _ | D_array _ -> ()
  | D_type js | D_state js | D_value js -> visit_jtype f js
  | D_loose(id,js) | D_safe(id,js) | D_order(id,js) -> f id ; visit_jtype f js
  | D_record fds -> List.iter (visit_field f) fds
  | D_request rq -> visit_request f rq

let visit_decl f { d_kind } = visit_dkind f d_kind

let visit_package_decl f { p_content } =
  List.iter (fun { d_ident } -> f d_ident) p_content

let visit_package_used f { p_content } =
  List.iter (visit_decl f) p_content

let resolve ?(keywords=[]) pkg =
  let scope = Scope.create pkg.p_plugin in
  List.iter (Scope.reserve scope) keywords ;
  visit_package_decl (Scope.declare scope) pkg ;
  visit_package_used (Scope.use scope) pkg ;
  Scope.resolve scope

(* -------------------------------------------------------------------------- *)
(* --- Server API                                                         --- *)
(* -------------------------------------------------------------------------- *)

type package = {
  pkgInfo : packageInfo ; (* with empty decl *)
  mutable revDecl : declInfo list ; (* in reverse order *)
}

let field fd = fd.fd_name , fd.fd_type

let name_of_package ?sep pkg = name_of_pkginfo ?sep pkg.pkgInfo

let registry = ref IdSet.empty (* including packages *)
let packages = ref [] (* in reverse order *)
let collection = ref None (* computed *)

let name_re = Str.regexp "^[a-zA-Z0-9]+$"
let package_re = Str.regexp "^[a-z0-9]+\\(\\.[a-z0-9]+\\)*$"

let check_package pkg =
  if not (Str.string_match package_re pkg 0) then
    Senv.fatal
      "Invalid package identifier %S (use dot separated lowercase names)"
      pkg

let check_name name =
  if not (Str.string_match name_re name 0) then
    Senv.fatal
      "Invalid identifier %S (use « camlCased » names)" name

let register_ident id =
  if IdSet.mem id !registry then
    Senv.fatal "Duplicate identifier '%a'" pp_ident id ;
  registry := IdSet.add id !registry

let resolve_readme ~plugin = function
  | None -> None
  | Some readme ->
    let file =
      match plugin with
      | Kernel ->
        Printf.sprintf "%s/server/%s" (Fc_config.datadir:>string) readme
      | Plugin name ->
        Printf.sprintf "%s/%s/server/%s" (Fc_config.datadir:>string) name readme
    in Some file

(* -------------------------------------------------------------------------- *)
(* --- Declarations                                                       --- *)
(* -------------------------------------------------------------------------- *)

let package ?plugin ?name ~title ?(descr=[]) ?readme () =
  let plugin = match plugin with None -> Kernel | Some p -> Plugin p in
  let pkgname = match name with
    | None -> []
    | Some pkg -> check_package pkg ; String.split_on_char '.' pkg in
  let pkgid = { plugin ; package = pkgname ; name = "*"} in
  let pkgInfo = {
    p_plugin = plugin ;
    p_package = pkgname ;
    p_title = title ;
    p_descr = descr ;
    p_readme = resolve_readme ~plugin readme ;
    p_content = [] ;
  } in
  let package = { pkgInfo ; revDecl=[] } in
  register_ident pkgid ;
  collection := None ;
  packages := package :: !packages ;
  package

let declare_id ~package:pkg ~name ?(descr=[]) decl =
  check_name name ;
  let { p_plugin = plugin ; p_package = package } = pkg.pkgInfo in
  let ident = { plugin ; package ; name } in
  let decl = { d_ident=ident ; d_descr=descr ; d_kind=decl } in
  register_ident ident ;
  pkg.revDecl <- decl :: pkg.revDecl ; ident

let declare ~package ~name ?descr decl =
  let _id = declare_id ~package ~name ?descr decl in ()

let update ~package:pkg ~name decl =
  pkg.revDecl <- List.map
      (fun curr ->
         if curr.d_ident.name = name then
           { curr with d_kind = decl }
         else curr
      ) pkg.revDecl

let iter f =
  List.iter f @@
  match !collection with
  | Some pkgs -> pkgs
  | None ->
    let pkgs =
      List.sort (fun a b -> Std.compare a.p_plugin b.p_plugin) @@
      List.rev_map
        (fun pkg -> { pkg.pkgInfo with p_content = List.rev pkg.revDecl })
        !packages
    in collection := Some pkgs ; pkgs

(* -------------------------------------------------------------------------- *)
(* --- JSON To MarkDown                                                   --- *)
(* -------------------------------------------------------------------------- *)

let key kd = Md.plain (Printf.sprintf "`#%s`" kd)
let index kd = Md.plain (Printf.sprintf "`#0%s`" kd)
let litteral tag = Md.plain (Printf.sprintf "`\"%s\"`" tag)

type pp = {
  self: Md.text ;
  ident: ident -> Md.text ;
}

let rec md_jtype pp = function
  | Jany -> Md.emph "any"
  | Jself -> pp.self
  | Jnull -> Md.emph "null"
  | Jnumber -> Md.emph "number"
  | Jboolean -> Md.emph "boolean"
  | Jstring | Jalpha -> Md.emph "string"
  | Jtag a -> litteral a
  | Jkey kd -> key kd
  | Jindex kd -> index kd
  | Jdata id | Jenum id -> pp.ident id
  | Joption js -> protect pp js @ Md.code "?"
  | Jtuple js -> Md.code "[" @ md_jlist pp "," js @ Md.code "]"
  | Junion js -> md_jlist pp "|" js
  | Jarray js | Jlist js -> protect pp js @ Md.code "[]"
  | Jrecord fjs -> Md.code "{" @ fields pp fjs @ Md.code "}"
  | Jdict js ->
    Md.code "{[key]:" @ md_jtype pp js @ Md.code "}"

and md_jlist pp sep js =
  Md.glue ~sep:(Md.plain sep)  (List.map (md_jtype pp) js)

and fields pp fjs =
  Md.glue ~sep:(Md.plain ",") @@
  List.map (fun (fd,js) ->
      litteral fd @
      match js with
      | Joption js -> Md.code ":?" @ md_jtype pp js
      | _ -> Md.code ":" @ md_jtype pp js
    ) fjs

and protect names js =
  match js with
  | Junion _ -> Md.code "(" @ md_jtype names js @ Md.code ")"
  | _ -> md_jtype names js

(* -------------------------------------------------------------------------- *)
(* --- Tags & Fields                                                      --- *)
(* -------------------------------------------------------------------------- *)

let md_tags ?(title="Tags") (tags : tagInfo list) =
  let header = Md.[
      plain title, Left;
      plain "Value", Left;
      plain "Description", Left
    ] in
  let row tg = [
    tg.tg_label ;
    litteral tg.tg_name ;
    tg.tg_descr ;
  ] in
  Md.{ caption = None ; header ; content = List.map row tags  }

let md_fields ?(title="Field") pp (fields : fieldInfo list) =
  let header = Md.[
      plain title, Left;
      plain "Format", Center;
      plain "Description", Left;
    ] in
  let row f =
    match f.fd_type with
    | Joption js -> [
        litteral f.fd_name @ Md.plain "(opt.)" ;
        md_jtype pp js ;
        f.fd_descr ;
      ]
    | _ -> [
        litteral f.fd_name ;
        md_jtype pp f.fd_type ;
        f.fd_descr ;
      ]
  in
  Md.{ caption = None ; header ; content = List.map row fields }

(* -------------------------------------------------------------------------- *)
(* --- Printer                                                            --- *)
(* -------------------------------------------------------------------------- *)

let pp_jtype fmt js =
  let scope = Scope.create Kernel in
  visit_jtype (Scope.use scope) js ;
  let ns = Scope.resolve scope in
  let self = Md.emph "self" in
  let ident id = Md.emph (IdMap.find id ns) in
  Markdown.pp_text fmt (md_jtype { self ; ident } js)

(* -------------------------------------------------------------------------- *)
