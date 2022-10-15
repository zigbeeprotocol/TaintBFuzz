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

(* To avoid listing declarations several times, we use their locations
   as proxies. However, we cannot directly compare locations, since static
   (re-)definitions, as well as prototypes included several times,
   have locations which are physically different (pos_cnum)
   despite being semantically identical (same file/line/column).
   The module below provides a hash table using the equality function
   corresponding to our needs.
*)
module SemanticLocs : sig
  include Hashtbl.S with type key = Cil_datatype.Location.t
  val is_empty: 'a t -> bool
  val keys: 'a t -> key list (* sorted w.r.t. cmp_start_semantic *)
  val elements: 'a t -> (key * 'a) list (* sorted w.r.t. cmp_start_semantic *)
end =
struct
  include
    Hashtbl.Make(struct
      type t = Cil_datatype.Location.t
      let equal = Cil_datatype.Location.equal_start_semantic
      let hash (b, _e) = Hashtbl.hash (b.Filepath.pos_path, b.Filepath.pos_lnum)
    end)
  let is_empty tbl = length tbl = 0
  let keys tbl =
    let l = fold (fun loc _ acc -> loc :: acc) tbl [] in
    List.sort Cil_datatype.Location.compare_start_semantic l
  let elements tbl =
    let l = fold (fun loc v acc -> (loc, v) :: acc) tbl [] in
    List.sort (fun (l1, _v1) (l2, _v2) ->
        Cil_datatype.Location.compare_start_semantic l1 l2) l
end

module Self = Plugin.Register
    (struct
      let name = "list-functions"
      let shortname = "list-functions"
      let help = "prints the list of function definitions and declarations, \
                  along with their locations and number of statements, \
                  in text or JSON format"
    end)

module PrintLibc =
  Self.False
    (struct
      let option_name = "-list-functions-libc"
      let help = "whether to print functions located within Frama-C's libc \
                  directory. Default: false"
    end)

module PrintDeclarations =
  Self.False
    (struct
      let option_name = "-list-functions-declarations"
      let help = "whether to print function declarations. Default: false"
    end)

module Output =
  Self.Filepath
    (struct
      let option_name = "-list-functions-output"
      let arg_name = "filename"
      let existence = Filepath.Indifferent
      let file_kind = "json"
      let help = "where to save the output, in JSON format. If omitted', \
                  then output to stdout in text format instead"
    end)

type funinfo = {
  name : string;
  declarations : unit SemanticLocs.t;
  definitions : int (*number of statements*) SemanticLocs.t;
  (* Note: only static functions can have multiple definitions *)
}

class stmt_count_visitor =
  object
    inherit Visitor.frama_c_inplace
    val count = ref 0
    method! vstmt_aux _s =
      incr count;
      Cil.DoChildren
    method get = !count
  end

(* To find good locations for declarations and definitions, we use different
   methods:
   - For declarations, the Cabs AST information is much better than the Cil
     one, which erases declarations when a definition is found;
   - For definitions, the information seems to be equivalent, so we use the
     one in Kernel_function.
*)

(* Due to the fact that the Cabs AST contains no fc_stdlib attributes, we use a
   location-based approach. *)
let located_within_framac_libc loc =
  let pos = fst loc in
  Filepath.is_relative ~base_name:Fc_config.framac_libc pos.Filepath.pos_path

class fun_cabs_visitor print_libc = object(self)
  inherit Cabsvisit.nopCabsVisitor

  val decls : (string, 'a SemanticLocs.t) Hashtbl.t = Hashtbl.create 7
  method get_decls = decls

  method private get_single_name (_spec, (name, _, _, _)) = name
  method private get_name (name, _, _, _) = name

  method private add_loc table name loc =
    if print_libc || not (located_within_framac_libc loc) then
      let locs_table =
        try
          Hashtbl.find table name
        with
        | Not_found ->
          let t = SemanticLocs.create 1 in
          Hashtbl.replace table name t;
          t
      in
      SemanticLocs.replace locs_table loc ()

  method! vdef def =
    let open Cabs in
    match def with
    | FUNDEF _ ->
      (* we will use Cil information anyway *)
      Cil.SkipChildren
    | DECDEF (_, (_, name_list), loc) ->
      List.iter
        (function
          | ((name, PROTO _, _, _), _) ->
            self#add_loc decls name loc
          | _ -> ()
        ) name_list;
      Cil.SkipChildren
    | _ ->
      Cil.DoChildren

end

let print_json (fp : Filepath.Normalized.t) funinfos_json =
  try
    let oc = open_out (fp:>string) in
    let fmt = Format.formatter_of_out_channel oc in
    Json.pp fmt funinfos_json;
    Format.fprintf fmt "@.";
    close_out oc;
    Self.debug "List written to: %a" Filepath.Normalized.pretty fp
  with Sys_error msg ->
    Self.abort "cannot write JSON to %a: %s"
      Filepath.Normalized.pretty fp msg

let pp_semlocs fmt t =
  Format.fprintf fmt "%a"
    (Pretty_utils.pp_list ~sep:", " Cil_datatype.Location.pretty)
    (SemanticLocs.keys t)

let pp_loc_size fmt loc_size =
  let (loc, size) = loc_size in
  Format.fprintf fmt "%a (%d statement%s)"
    Cil_datatype.Location.pretty loc size (if size <> 1 then "s" else "")

let pp_definitions fmt defs =
  Format.fprintf fmt "%a"
    (Pretty_utils.pp_list ~sep:", " pp_loc_size)
    (SemanticLocs.elements defs)

let print_text funinfos =
  List.iter (fun fi ->
      if PrintDeclarations.get () ||
         not (SemanticLocs.is_empty fi.definitions) then
        begin
          Format.printf "%s:" fi.name;
          begin
            if not (SemanticLocs.is_empty fi.definitions) then
              Format.printf " defined at %a;"
                pp_definitions fi.definitions
          end;
          if PrintDeclarations.get () &&
             not (SemanticLocs.is_empty fi.declarations) then
            Format.printf " declared at %a" pp_semlocs fi.declarations;
          if SemanticLocs.(is_empty fi.definitions && is_empty fi.declarations)
          then
            Format.printf " called but never declared nor defined";
          Format.printf "@."
        end
    ) funinfos

let get_size kf =
  let stmt_count_vis = new stmt_count_visitor in
  ignore Visitor.(visitFramacKf (stmt_count_vis :> frama_c_inplace) kf);
  stmt_count_vis#get

let definitions_with_size name =
  let kfs =
    List.filter Kernel_function.is_definition
      (Globals.Functions.find_all_by_orig_name name)
  in
  let defs_with_size = SemanticLocs.create (List.length kfs) in
  List.iter (fun kf ->
      let n = get_size kf in
      let loc = Kernel_function.get_location kf in
      SemanticLocs.add defs_with_size loc n
    ) kfs;
  defs_with_size

let json_string_of_loc loc =
  `String (Format.asprintf "%a" Cil_datatype.Location.pretty loc)

let json_list_of_loc_tbl tbl =
  let keys = SemanticLocs.keys tbl in
  `List (List.map json_string_of_loc keys)

let json_array_of_loc_size (loc, size) =
  `Assoc [("location", json_string_of_loc loc); ("statements", `Int size)]

let json_list_of_loc_size_tbl tbl =
  let elements = SemanticLocs.elements tbl in
  `List (List.map json_array_of_loc_size elements)

let run () =
  if List.length (File.get_all ()) < 1 then begin
    Self.abort "no input files";
  end;
  let cabs_files = Ast.UntypedFiles.get () in
  let vis = new fun_cabs_visitor (PrintLibc.get ()) in
  List.iter (fun file ->
      ignore Cabsvisit.(visitCabsFile (vis :> nopCabsVisitor) file)
    ) cabs_files;
  let decls = vis#get_decls in
  let defs_without_decls = Globals.Functions.fold (fun kf acc ->
      if Kernel_function.is_definition kf then begin
        let orig_name = (Kernel_function.get_vi kf).vorig_name in
        if Hashtbl.mem decls orig_name then acc
        else Datatype.String.Set.add orig_name acc
      end
      else acc
    ) Datatype.String.Set.empty
  in
  let funinfos =
    Hashtbl.fold (fun name declarations acc ->
        let definitions = definitions_with_size name in
        let fi = { name; definitions; declarations } in
        fi :: acc
      ) decls []
  in
  (* add data for defined functions not present in 'decls' *)
  let funinfos =
    Datatype.String.Set.fold (fun orig_name acc ->
        if not (Hashtbl.mem decls orig_name) then begin
          let definitions = definitions_with_size orig_name in
          let fi = { name = orig_name; definitions;
                     declarations = SemanticLocs.create 0 }
          in
          fi :: acc
        end else
          acc
      ) defs_without_decls funinfos
  in
  let funinfos = List.sort
      (fun fi1 fi2 -> Extlib.compare_ignore_case fi1.name fi2.name) funinfos
  in
  let outfp = Output.get () in
  if Filepath.Normalized.is_empty outfp then
    print_text funinfos
  else
    let funinfos_json = `List (List.map (fun fi ->
        let definitions =
          if SemanticLocs.is_empty fi.definitions then []
          else
            [("definitions", json_list_of_loc_size_tbl fi.definitions)]
        in
        let declarations =
          if SemanticLocs.is_empty fi.declarations then []
          else
            [("declarations", json_list_of_loc_tbl fi.declarations)]
        in
        `Assoc [(fi.name, `Assoc (definitions @ declarations))]
      ) funinfos)
    in
    print_json outfp funinfos_json

let () = Db.Main.extend run
