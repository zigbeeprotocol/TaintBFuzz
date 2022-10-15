(****************************************************************************)
(*                                                                          *)
(*  Copyright (C) 2001-2003                                                 *)
(*   George C. Necula    <necula@cs.berkeley.edu>                           *)
(*   Scott McPeak        <smcpeak@cs.berkeley.edu>                          *)
(*   Wes Weimer          <weimer@cs.berkeley.edu>                           *)
(*   Ben Liblit          <liblit@cs.berkeley.edu>                           *)
(*  All rights reserved.                                                    *)
(*                                                                          *)
(*  Redistribution and use in source and binary forms, with or without      *)
(*  modification, are permitted provided that the following conditions      *)
(*  are met:                                                                *)
(*                                                                          *)
(*  1. Redistributions of source code must retain the above copyright       *)
(*  notice, this list of conditions and the following disclaimer.           *)
(*                                                                          *)
(*  2. Redistributions in binary form must reproduce the above copyright    *)
(*  notice, this list of conditions and the following disclaimer in the     *)
(*  documentation and/or other materials provided with the distribution.    *)
(*                                                                          *)
(*  3. The names of the contributors may not be used to endorse or          *)
(*  promote products derived from this software without specific prior      *)
(*  written permission.                                                     *)
(*                                                                          *)
(*  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS     *)
(*  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT       *)
(*  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS       *)
(*  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE          *)
(*  COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,     *)
(*  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,    *)
(*  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;        *)
(*  LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER        *)
(*  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT      *)
(*  LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN       *)
(*  ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE         *)
(*  POSSIBILITY OF SUCH DAMAGE.                                             *)
(*                                                                          *)
(*  File modified by CEA (Commissariat à l'énergie atomique et aux          *)
(*                        énergies alternatives)                            *)
(*               and INRIA (Institut National de Recherche en Informatique  *)
(*                          et Automatique).                                *)
(****************************************************************************)

open Cil_datatype
open Cil_types

let typeAddVolatile typ = Cil.typeAddAttributes [Attr ("volatile", [])] typ

module Frama_c_builtins =
  State_builder.Hashtbl
    (Datatype.String.Hashtbl)
    (Cil_datatype.Varinfo)
    (struct
      let name = "Cil.Frama_c_Builtins"
      let dependencies = []
      let size = 3
    end)

let () = Cil.dependency_on_ast Frama_c_builtins.self

let is_builtin v = Cil.hasAttribute "FC_BUILTIN" v.vattr

let is_unused_builtin v = is_builtin v && not v.vreferenced


(* [VP] Should we projectify this ?*)
let special_builtins_table = ref Datatype.String.Set.empty
let special_builtins = Queue.create ()

let is_special_builtin s =
  Queue.fold (fun res f -> res || f s) false special_builtins

let add_special_builtin_family f = Queue.add f special_builtins

let add_special_builtin s =
  special_builtins_table := Datatype.String.Set.add s !special_builtins_table

let () = add_special_builtin_family
    (fun s -> Datatype.String.Set.mem s !special_builtins_table)

let () = List.iter add_special_builtin
    [ "__builtin_stdarg_start"; "__builtin_va_arg";
      "__builtin_va_start"; "__builtin_expect"; "__builtin_next_arg"; ]

module Builtin_functions =
  State_builder.Hashtbl
    (Datatype.String.Hashtbl)
    (Datatype.Triple(Typ)(Datatype.List(Typ))(Datatype.Bool))
    (struct
      let name = "Builtin_functions"
      let dependencies = [ Cil.selfMachine ]
      let size = 49
    end)

(* [add_builtin ?prefix s t l b] adds the function [prefix ^ s] to the list of
   built-ins. [t] is the return type and [l] is the list of parameter types.
   [b] is true if the built-in is variadic, false otherwise. *)
let add_builtin ?(prefix="__builtin_") s t l b =
  Builtin_functions.add (prefix ^ s) (t, l, b)

let () = Cil.registerAttribute "FC_BUILTIN" (AttrName true)

let custom_builtins = Queue.create ()

let add_custom_builtin f = Queue.add f custom_builtins

let register_custom_builtin (name, rt, prms, isva) =
  Builtin_functions.add name (rt,prms,isva)

(* Table Builtin_templates is similar to Builtin_functions,
   but with a few differences:
   1. it lists all _known_ builtins, even those not registered (available)
      under the current machdep.
   2. It lists the 'generic' builtin names, not their 'typed' versions,
      e.g. '__sync_add_and_fetch' instead of '__sync_add_and_fetch_int32_t'.
   3. It can refer to "generic" type 'type', as in GCC's docs, since its types
      are only strings, not actual CIL types.
   This table mirrors the contents of the 'data' field of file
   'compiler_builtins.json'.
*)

type compiler = GCC | MSVC | Not_MSVC

type builtin_template = {
  name: string;
  compiler: compiler option;
  rettype: string;
  args: string list;
  types: string list option;
  variadic: bool;
}

let to_compiler s =
  if s = "gcc" then GCC
  else if s = "msvc" then MSVC
  else if s = "!msvc" then Not_MSVC
  else
    Kernel.fatal "invalid compiler '%s' in compiler_builtins JSON" s

let string_of_compiler = function
  | GCC -> "GCC-based"
  | MSVC -> "MSVC-based"
  | Not_MSVC -> "not MSVC-based"

module Builtin_template = struct
  let dummy =
    { name = "";
      compiler = None;
      rettype = "";
      args = [];
      types = None;
      variadic = false;
    }
  include Datatype.Make_with_collections
      (struct
        type t = builtin_template
        let name = "Builtin_template"
        let reprs = [ dummy ]
        let compare b1 b2 = String.compare b1.name b2.name
        let hash b = Datatype.String.hash b.name
        let equal b1 b2 = b1.name = b2.name
        let copy = Datatype.identity
        let internal_pretty_code = Datatype.undefined
        let pretty fmt b =
          Format.fprintf fmt "%s %s(%a%s)"
            b.rettype b.name
            (Pretty_utils.pp_list ~sep:", " Format.pp_print_string) b.args
            (if b.variadic then ", ..." else "")
        let rehash = Datatype.identity
        let structural_descr = Structural_descr.t_abstract
        let mem_project = Datatype.never_any_project
        let varname b = "_cb_" ^ b.name
      end)
end
module Builtin_templates =
  State_builder.Hashtbl
    (Datatype.String.Hashtbl)
    (Builtin_template)
    (struct
      let name = "Builtin_templates"
      let dependencies = []
      let size = 200
    end)

module Gcc_builtin_templates_loaded =
  State_builder.Ref
    (Datatype.Bool)
    (struct
      let name = "Cil_builtins.Gcc_builtin_templates_loaded"
      let dependencies = [ Builtin_templates.self ]
      let default () = false
    end)

(* An actual instance of a builtin_template, with actual types. *)
type builtin = {
  name: string;
  compiler: compiler option;
  rettype: typ option;
  args: typ option list;
  variadic: bool;
}

module Json =
struct
  open Yojson.Basic
  open Util

  let parse fp =
    Kernel.feedback ~dkey:Kernel.dkey_builtins "Parsing builtins file: %a"
      Datatype.Filepath.pretty fp;
    let json = Json.from_file fp in
    member "data" json

  let init_builtin_templates ?default_compiler fp =
    let json = parse fp in
    List.iter (fun (name, entry) ->
        let compiler =
          if default_compiler <> None then default_compiler
          else
            entry |> member "compiler" |> to_string_option |>
            Option.map to_compiler
        in
        let rettype = entry |> member "rettype" |> to_string in
        let args = entry |> member "args" |> to_list |> List.map to_string in
        let variadic =
          entry |> member "variadic" |> to_bool_option |> Option.is_some
        in
        let types =
          match entry |> member "types" with
          | `Null -> None
          | `List l -> Some (List.map to_string l)
          | _ ->
            Kernel.fatal "invalid 'types': expected list (in %a)"
              Datatype.Filepath.pretty fp
        in
        let cb = { name; compiler; rettype; args; types; variadic} in
        Builtin_templates.replace name cb
      ) (json |> to_assoc)

end

(* For performance, this table provides O(1) lookups between type names
   and the underlying Cil types. Some types may be unavailable in some
   machdeps, so the table returns an option type.
   Note that the type strings must follow a strict format (also used
   in gcc_builtins.json), with a single space between type names and
   asterisks (for pointers); otherwise we would have to do some expensive
   matching.
*)
let build_type_table () : (string, typ option) Hashtbl.t =
  let int8_t = Some Cil.scharType in
  let int16_t = try Some (Cil.int16_t ()) with Not_found -> None in
  let int32_t = try Some (Cil.int32_t ()) with Not_found -> None in
  let int64_t = try Some (Cil.int64_t ()) with Not_found -> None in
  let uint8_t = Some Cil.ucharType in
  let uint16_t = try Some (Cil.uint16_t ()) with Not_found -> None in
  let uint32_t = try Some (Cil.uint32_t ()) with Not_found -> None in
  let uint64_t = try Some (Cil.uint64_t ()) with Not_found -> None in
  let ptr_of = Option.map (fun t -> TPtr(t,[])) in
  let volatile_ptr_of = Option.map (fun t -> TPtr(typeAddVolatile t,[])) in
  let types =
    [
      ("__builtin_va_list",
       Some (if Cil.theMachine.theMachine.has__builtin_va_list
             then TBuiltin_va_list []
             else Cil.voidPtrType));
      ("char *", Some Cil.charPtrType);
      ("char const *", Some Cil.charConstPtrType);
      ("double", Some Cil.doubleType);
      ("double *", Some (TPtr(Cil.doubleType,[])));
      ("float", Some Cil.floatType);
      ("float *", Some (TPtr(Cil.floatType,[])));
      ("int", Some Cil.intType);
      ("int *", Some Cil.intPtrType);
      ("int volatile *", Some (TPtr(typeAddVolatile Cil.intType,[])));
      ("long", Some Cil.longType);
      ("long double", Some Cil.longDoubleType);
      ("long double *", Some (TPtr(Cil.longDoubleType,[])));
      ("long long", Some Cil.longLongType);
      ("long long volatile *", Some (TPtr(typeAddVolatile Cil.longLongType,[])));
      ("short", Some Cil.shortType);
      ("short volatile *", Some (TPtr(typeAddVolatile Cil.shortType,[])));
      ("signed char", Some Cil.scharType);
      ("signed char volatile *", Some (TPtr(typeAddVolatile Cil.scharType,[])));
      ("unsigned char", Some Cil.ucharType);
      ("unsigned char volatile *", Some (TPtr(typeAddVolatile Cil.ucharType,[])));
      ("unsigned int", Some Cil.uintType);
      ("unsigned int volatile *", Some (TPtr(typeAddVolatile Cil.uintType,[])));
      ("unsigned long", Some Cil.ulongType);
      ("unsigned long long", Some Cil.ulongLongType);
      ("unsigned long long volatile *", Some (TPtr(typeAddVolatile Cil.ulongLongType,[])));
      ("unsigned short", Some Cil.ushortType);
      ("unsigned short volatile *", Some (TPtr(typeAddVolatile Cil.ushortType,[])));
      ("void", Some Cil.voidType);
      ("void *", Some Cil.voidPtrType);
      ("void const *", Some Cil.voidConstPtrType);
      ("size_t", Some Cil.theMachine.typeOfSizeOf);
      ("int8_t", int8_t);
      ("int16_t", int16_t);
      ("int32_t", int32_t);
      ("int64_t", int64_t);
      ("uint8_t", uint8_t);
      ("uint16_t", uint16_t);
      ("uint32_t", uint32_t);
      ("uint64_t", uint64_t);
      ("int8_t *", ptr_of int8_t);
      ("int16_t *", ptr_of int16_t);
      ("int32_t *", ptr_of int32_t);
      ("int64_t *", ptr_of int64_t);
      ("uint8_t *", ptr_of uint8_t);
      ("uint16_t *", ptr_of uint16_t);
      ("uint32_t *", ptr_of uint32_t);
      ("uint64_t *", ptr_of uint64_t);
      ("int8_t volatile *", volatile_ptr_of int8_t);
      ("int16_t volatile *", volatile_ptr_of int16_t);
      ("int32_t volatile *", volatile_ptr_of int32_t);
      ("int64_t volatile *", volatile_ptr_of int64_t);
      ("uint8_t volatile *", volatile_ptr_of uint8_t);
      ("uint16_t volatile *", volatile_ptr_of uint16_t);
      ("uint32_t volatile *", volatile_ptr_of uint32_t);
      ("uint64_t volatile *", volatile_ptr_of uint64_t);
    ] in
  Hashtbl.of_seq (List.to_seq types)

(* Note that [s] (the type string) follows a stricter format than the ones
   allowed by the C standard w.r.t. type names; a single space must be
   present between type names and asterisks. *)
let parse_type ?(template="") type_table s =
  try
    if String.get s 0 == 'T' then
      (* replace 'T' (always at the beginning) with the template *)
      let typ = template ^ (String.sub s 1 (String.length s - 1)) in
      Hashtbl.find type_table typ
    else
      Hashtbl.find type_table s
  with Not_found ->
    Kernel.fatal "invalid type '%s' in compiler_builtins JSON" s

let is_machdep_active compiler =
  match compiler, Cil.gccMode (), Cil.msvcMode () with
  | None, _, _ (* always active *)
  | Some GCC, true, _
  | Some MSVC, _, true
  | Some Not_MSVC, _, false -> true
  | _, _, _ -> false

let add_builtin_if_active b =
  if is_machdep_active b.compiler then begin
    Kernel.feedback ~dkey:Kernel.dkey_builtins
      "adding builtin: %a %s(%a%s)"
      Cil_datatype.Typ.pretty (Option.get b.rettype) b.name
      (Pretty_utils.pp_list ~sep:", " Cil_datatype.Typ.pretty)
      (List.map Option.get b.args)
      (if b.variadic then ", ..." else "")
    ;
    add_builtin ~prefix:"" b.name (Option.get b.rettype)
      ((List.map Option.get) b.args) b.variadic
  end

(* Instantiates builtins according to the types in the template.
   In some machdeps, there may be missing types (e.g. int16_t);
   such elements are not instantiated in the resulting list.
   If the template has no 'types' member, at most a single
   builtin will be instantiated. *)
let instantiate_available_templates type_table name (entry : builtin_template) =
  let compiler = entry.compiler in
  let variadic = entry.variadic in
  let make_builtin_as_list ?template name =
    let to_type_opt = parse_type ?template type_table in
    let rettype = to_type_opt entry.rettype in
    let args = List.map to_type_opt entry.args in
    if rettype = None || List.exists (fun arg -> arg = None) args
    then (* unavailable type: skip builtin *) []
    else
      let name =
        Option.fold ~none:name ~some:(fun t -> name ^ "_" ^ t) template
      in
      [{ name; compiler; rettype; args; variadic }]
  in
  match entry.types with
  | Some types ->
    List.fold_left (fun acc template ->
        (make_builtin_as_list ~template name) @ acc
      ) [] types
  | None ->
    make_builtin_as_list name

let init_gcc_builtin_templates () =
  let fp =
    Datatype.Filepath.concat ~existence:Filepath.Must_exist
      Fc_config.datadir "compliance/gcc_builtins.json"
  in
  Json.init_builtin_templates ~default_compiler:GCC fp;
  Gcc_builtin_templates_loaded.set true

let init_other_builtin_templates () =
  let fp =
    Datatype.Filepath.concat ~existence:Filepath.Must_exist
      Fc_config.datadir "compliance/compiler_builtins.json"
  in
  Json.init_builtin_templates fp

let init_builtins_from_json () =
  (* For performance reasons, we avoid loading GCC builtins unless we are
     using a GCC machdep *)
  if Cil.gccMode () then init_gcc_builtin_templates ();
  init_other_builtin_templates ();
  let type_table = build_type_table () in
  Builtin_templates.iter (fun name entry ->
      (* In the JSON file, each entry is possibly a template for
         several type-specialized functions *)
      let builtins = instantiate_available_templates type_table name entry in
      List.iter add_builtin_if_active builtins
    )

let init_builtins () =
  if not (Cil.selfMachine_is_computed ()) then
    Kernel.fatal ~current:true "You must call initCIL before init_builtins" ;
  if Builtin_functions.length () <> 0 then
    Kernel.fatal ~current:true "Cil builtins already initialized." ;
  init_builtins_from_json ();
  Queue.iter (fun f -> register_custom_builtin (f())) custom_builtins

(** This is used as the location of the prototypes of builtin functions. *)
let builtinLoc: location = Location.unknown

let () =
  Cil.init_builtins_ref := init_builtins
