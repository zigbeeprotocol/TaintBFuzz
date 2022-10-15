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

open Data
module Md = Markdown
module Js = Yojson.Basic.Util
module Pkg = Package
open Cil_types

let package = Pkg.package ~title:"Ast Services" ~name:"ast" ~readme:"ast.md" ()

(* -------------------------------------------------------------------------- *)
(* --- Marker Cache System                                                --- *)
(* -------------------------------------------------------------------------- *)

let logic_environment () =
  let open Logic_typing in
  Lenv.empty () |> append_pre_label |> append_init_label |> append_here_label

module Key = Datatype.Pair(Cil_datatype.Stmt)(Cil_datatype.Term)
module Cache = Hashtbl.Make(Key)

let get_term kf term =
  let env = logic_environment () in
  try Some (!Db.Properties.Interp.term ~env kf term)
  with Logic_interp.Error _ | Parsing.Parse_error -> None

let key_of_localizable =
  let open Printer_tag in
  function
  | PStmt _ | PStmtStart _ | PTermLval _ | PVDecl _ | PGlobal _ | PIP _ -> None
  | PLval (_, Kglobal, _) | PExp (_, Kglobal, _) -> None
  | PLval (kf, Kstmt stmt, lval) ->
    let str = Format.asprintf "%a" Cil_datatype.Lval.pretty lval in
    Option.(bind kf (fun kf -> get_term kf str) |> map (fun t -> (stmt, t)))
  | PExp (kf, Kstmt stmt, exp) ->
    let str = Format.asprintf "%a" Cil_datatype.Exp.pretty exp in
    Option.(bind kf (fun kf -> get_term kf str) |> map (fun t -> (stmt, t)))

let cache = Cache.create 10

(* -------------------------------------------------------------------------- *)
(* --- Compute Ast                                                        --- *)
(* -------------------------------------------------------------------------- *)

let () = Request.register ~package
    ~kind:`EXEC ~name:"compute"
    ~descr:(Md.plain "Ensures that AST is computed")
    ~input:(module Junit) ~output:(module Junit) Ast.compute

let changed_signal = Request.signal ~package ~name:"changed"
    ~descr:(Md.plain "Emitted when the AST has been changed")

let ast_update_hook f =
  Ast.add_hook_on_update f;
  Ast.apply_after_computed (fun _ -> f ())

let () = ast_update_hook (fun _ -> Request.emit changed_signal)

(* -------------------------------------------------------------------------- *)
(* --- File Positions                                                     --- *)
(* -------------------------------------------------------------------------- *)

module Position =
struct
  type t = Filepath.position

  let jtype = Data.declare ~package ~name:"source"
      ~descr:(Md.plain "Source file positions.")
      (Jrecord [
          "dir", Jstring;
          "base", Jstring;
          "file", Jstring;
          "line", Jnumber;
        ])

  let to_json p =
    let path = Filepath.(Normalized.to_pretty_string p.pos_path) in
    let file =
      if Server_parameters.has_relative_filepath ()
      then path
      else (p.Filepath.pos_path :> string)
    in
    `Assoc [
      "dir"  , `String (Filename.dirname path) ;
      "base" , `String (Filename.basename path) ;
      "file" , `String file ;
      "line" , `Int p.Filepath.pos_lnum ;
    ]

  let of_json js =
    let fail () = failure_from_type_error "Invalid source format" js in
    match js with
    | `Assoc assoc ->
      begin
        match List.assoc "file" assoc, List.assoc "line" assoc with
        | `String path, `Int line ->
          Log.source ~file:(Filepath.Normalized.of_string path) ~line
        | _, _ -> fail ()
        | exception Not_found -> fail ()
      end
    | _ -> fail ()

end

(* -------------------------------------------------------------------------- *)
(* ---  Printers                                                          --- *)
(* -------------------------------------------------------------------------- *)

(* The kind of a marker. *)
module MarkerKind = struct

  let kinds = Enum.dictionary ()

  let kind name =
    Enum.tag
      ~name
      ~descr:(Md.plain (String.capitalize_ascii name))
      kinds

  let expr = kind "expression"
  let lval = kind "lvalue"
  let decl = kind "declaration"
  let stmt = kind "statement"
  let glob = kind "global"
  let term = kind "term"
  let prop = kind "property"

  let () =
    Enum.set_lookup
      kinds
      (fun localizable ->
         let open Printer_tag in
         match localizable with
         | PStmt _ -> stmt
         | PStmtStart _ -> stmt
         | PVDecl _ -> decl
         | PLval _ -> lval
         | PExp _ -> expr
         | PTermLval _ -> term
         | PGlobal _ -> glob
         | PIP _ -> prop)

  let data =
    Request.dictionary
      ~package
      ~name:"markerKind"
      ~descr:(Md.plain "Marker kind")
      kinds

  include (val data : S with type t = Printer_tag.localizable)
end

module MarkerVar = struct

  let vars = Enum.dictionary ()

  let kind name =
    Enum.tag
      ~name
      ~descr:(Md.plain (String.capitalize_ascii name))
      vars

  let none = kind "none"
  let var = kind "variable"
  let fct = kind "function"

  let () =
    Enum.set_lookup
      vars
      (fun localizable ->
         let open Printer_tag in
         match localizable with
         | PLval (_, _, (Var vi, NoOffset))
         | PVDecl (_, _, vi)
         | PGlobal (GVar (vi, _, _)  | GVarDecl (vi, _)) ->
           if Cil.isFunctionType vi.vtype then fct else var
         | PGlobal (GFun _ | GFunDecl _) -> fct
         | PLval _ | PStmt _ | PStmtStart _
         | PExp _ | PTermLval _ | PGlobal _ | PIP _ -> none)

  let data =
    Request.dictionary
      ~package
      ~name:"markerVar"
      ~descr:(Md.plain "Marker variable")
      vars

  include (val data : S with type t = Printer_tag.localizable)
end

module Marker =
struct

  open Printer_tag

  type index = {
    tags : string Localizable.Hashtbl.t ;
    locs : (string,localizable) Hashtbl.t ;
  }

  let kid = ref 0

  let index () = {
    tags = Localizable.Hashtbl.create 0 ;
    locs = Hashtbl.create 0 ;
  }

  module TYPE : Datatype.S with type t = index =
    Datatype.Make
      (struct
        type t = index
        include Datatype.Undefined
        let reprs = [index()]
        let name = "Server.Jprinter.Index"
        let mem_project = Datatype.never_any_project
      end)

  module STATE = State_builder.Ref(TYPE)
      (struct
        let name = "Server.Jprinter.State"
        let dependencies = []
        let default = index
      end)

  let iter f =
    Localizable.Hashtbl.iter (fun key str -> f (key, str)) (STATE.get ()).tags

  let array =
    let model = States.model () in
    let () =
      States.column
        ~name:"kind"
        ~descr:(Md.plain "Marker kind")
        ~data:(module MarkerKind)
        ~get:fst
        model
    in
    let () =
      States.column
        ~name:"var"
        ~descr:(Md.plain "Marker variable")
        ~data:(module MarkerVar)
        ~get:fst
        model
    in
    let () =
      States.column
        ~name:"name"
        ~descr:(Md.plain "Marker short name")
        ~data:(module Jalpha)
        ~get:(fun (tag, _) -> Printer_tag.label tag)
        model
    in
    let () =
      States.column
        ~name:"descr"
        ~descr:(Md.plain "Marker declaration or description")
        ~data:(module Jstring)
        ~get:(fun (tag, _) -> Rich_text.to_string Printer_tag.pretty tag)
        model
    in
    let () =
      States.column
        ~name:"sloc"
        ~descr:(Md.plain "Source location")
        ~data:(module Position)
        ~get:(fun (tag, _) -> fst (Printer_tag.loc_of_localizable tag))
        model
    in
    States.register_array
      ~package
      ~name:"markerInfo"
      ~descr:(Md.plain "Marker information")
      ~key:snd ~keyType:Jstring
      ~iter ~add_reload_hook:ast_update_hook
      model

  let create_tag = function
    | PStmt(_,s) -> Printf.sprintf "#s%d" s.sid
    | PStmtStart(_,s) -> Printf.sprintf "#k%d" s.sid
    | PVDecl(_,_,v) -> Printf.sprintf "#v%d" v.vid
    | PLval _ -> Printf.sprintf "#l%d" (incr kid ; !kid)
    | PExp(_,_,e) -> Printf.sprintf "#e%d" e.eid
    | PTermLval _ -> Printf.sprintf "#t%d" (incr kid ; !kid)
    | PGlobal _ -> Printf.sprintf "#g%d" (incr kid ; !kid)
    | PIP _ -> Printf.sprintf "#p%d" (incr kid ; !kid)

  let create loc =
    let add_cache key = Cache.add cache key loc in
    key_of_localizable loc |> Option.iter add_cache;
    let { tags ; locs } = STATE.get () in
    try Localizable.Hashtbl.find tags loc
    with Not_found ->
      let tag = create_tag loc in
      Localizable.Hashtbl.add tags loc tag ;
      Hashtbl.add locs tag loc ;
      States.update array (loc, tag);
      tag

  let lookup tag = Hashtbl.find (STATE.get()).locs tag

  type t = localizable

  let markers = ref []
  let jmarker kd =
    let jt = Pkg.Jkey kd in markers := jt :: !markers ; jt

  let jstmt = jmarker "stmt"
  let jdecl = jmarker "decl"
  let jlval = jmarker "lval"
  let jexpr = jmarker "expr"
  let jterm = jmarker "term"
  let jglobal = jmarker "global"
  let jproperty = jmarker "property"

  let jtype = Data.declare ~package ~name:"marker"
      ~descr:(Md.plain "Localizable AST markers")
      Pkg.(Junion (List.rev !markers))

  let to_json loc = `String (create loc)
  let of_json js =
    try lookup (Js.to_string js)
    with Not_found -> Data.failure "not a localizable marker"

end

module Printer = Printer_tag.Make(Marker)

(* -------------------------------------------------------------------------- *)
(* --- Ast Data                                                           --- *)
(* -------------------------------------------------------------------------- *)

module Lval =
struct
  type t = kinstr * lval
  let jtype = Marker.jlval
  let to_json (kinstr, lval) =
    let kf = match kinstr with
      | Kglobal -> None
      | Kstmt stmt -> Some (Kernel_function.find_englobing_kf stmt)
    in
    Marker.to_json (PLval (kf, kinstr, lval))
  let of_json js =
    let open Printer_tag in
    match Marker.of_json js with
    | PLval (_, kinstr, lval) -> kinstr, lval
    | PVDecl (_, kinstr, vi) -> kinstr, Cil.var vi
    | PGlobal (GVar (vi, _, _) | GVarDecl (vi, _)) -> Kglobal, Cil.var vi
    | _ -> Data.failure "not a lval marker"
end

module Stmt =
struct
  type t = stmt
  let jtype = Marker.jstmt
  let to_json st =
    let kf = Kernel_function.find_englobing_kf st in
    Marker.to_json (PStmt(kf,st))
  let of_json js =
    let open Printer_tag in
    match Marker.of_json js with
    | PStmt(_,st) | PStmtStart(_,st) -> st
    | _ -> Data.failure "not a stmt marker"
end

module Ki =
struct
  type t = kinstr
  let jtype = Pkg.Joption Marker.jstmt
  let to_json = function
    | Kglobal -> `Null
    | Kstmt st -> Stmt.to_json st
  let of_json = function
    | `Null -> Kglobal
    | js -> Kstmt (Stmt.of_json js)
end

module Kf =
struct
  type t = kernel_function
  let jtype = Pkg.Jkey "fct"
  let to_json kf =
    `String (Kernel_function.get_name kf)
  let of_json js =
    let key = Js.to_string js in
    try Globals.Functions.find_by_name key
    with Not_found -> Data.failure "Undefined function '%s'" key
end

module Fundec =
struct
  type t = fundec
  let jtype = Pkg.Jkey "fundec"
  let to_json fundec =
    `String fundec.svar.vname
  let of_json js =
    let key = Js.to_string js in
    try Kernel_function.get_definition (Globals.Functions.find_by_name key)
    with Not_found | Kernel_function.No_Definition ->
      Data.failure "Undefined function definition '%s'" key
end

module KfMarker = struct
  type record
  let record : record Record.signature = Record.signature ()
  let fct = Record.field record ~name:"fct"
      ~descr:(Md.plain "Function") (module Kf)
  let marker = Record.field record ~name:"marker"
      ~descr:(Md.plain "Marker") (module Marker)

  let data =
    Record.publish ~package ~name:"location"
      ~descr:(Md.plain "Location: function and marker") record
  module R : Record.S with type r = record = (val data)
  type t = kernel_function * Printer_tag.localizable
  let jtype = R.jtype

  let to_json (kf, loc) =
    R.default |>
    R.set fct kf |>
    R.set marker loc |>
    R.to_json

  let of_json json =
    let r = R.of_json json in
    R.get fct r, R.get marker r
end

(* -------------------------------------------------------------------------- *)
(* --- Functions                                                          --- *)
(* -------------------------------------------------------------------------- *)

let () = Request.register ~package
    ~kind:`GET ~name:"getMainFunction"
    ~descr:(Md.plain "Get the current 'main' function.")
    ~input:(module Junit) ~output:(module Joption (Kf))
    begin fun () ->
      try Some (fst (Globals.entry_point ()))
      with Globals.No_such_entry_point _ -> None
    end

let () = Request.register ~package
    ~kind:`GET ~name:"getFunctions"
    ~descr:(Md.plain "Collect all functions in the AST")
    ~input:(module Junit) ~output:(module Jlist(Kf))
    begin fun () ->
      let pool = ref [] in
      Globals.Functions.iter (fun kf -> pool := kf :: !pool) ;
      List.rev !pool
    end

let () = Request.register ~package
    ~kind:`GET ~name:"printFunction"
    ~descr:(Md.plain "Print the AST of a function")
    ~input:(module Kf) ~output:(module Jtext)
    begin fun kf ->
      let libc = Kernel.PrintLibc.get () in
      try
        if not libc then Kernel.PrintLibc.set true ;
        let global = Kernel_function.get_global kf in
        let ast = Jbuffer.to_json Printer.pp_global global in
        if not libc then Kernel.PrintLibc.set false ; ast
      with err ->
        if not libc then Kernel.PrintLibc.set false ; raise err
    end

module Functions =
struct

  let key kf = Printf.sprintf "kf#%d" (Kernel_function.get_id kf)

  let signature kf =
    let global = Kernel_function.get_global kf in
    let libc = Kernel.PrintLibc.get () in
    try
      if not libc then Kernel.PrintLibc.set true ;
      let txt = Rich_text.to_string Printer_tag.pretty (PGlobal global) in
      if not libc then Kernel.PrintLibc.set false ;
      if Kernel_function.is_entry_point kf then (txt ^ " /* main */") else txt
    with err ->
      if not libc then Kernel.PrintLibc.set false ; raise err

  let is_builtin kf =
    Cil_builtins.is_builtin (Kernel_function.get_vi kf)

  let is_stdlib kf =
    let vi = Kernel_function.get_vi kf in
    Cil.is_in_libc vi.vattr

  let is_eva_analyzed kf =
    if Db.Value.is_computed () then !Db.Value.is_called kf else false

  let iter f =
    Globals.Functions.iter
      (fun kf ->
         let name = Kernel_function.get_name kf in
         if not (Ast_info.is_frama_c_builtin name) then f kf)

  let array : kernel_function States.array =
    begin
      let model = States.model () in
      States.column model
        ~name:"name"
        ~descr:(Md.plain "Name")
        ~data:(module Data.Jalpha)
        ~get:Kernel_function.get_name ;
      States.column model
        ~name:"signature"
        ~descr:(Md.plain "Signature")
        ~data:(module Data.Jstring)
        ~get:signature ;
      States.column model
        ~name:"main"
        ~descr:(Md.plain "Is the function the main entry point")
        ~data:(module Data.Jbool)
        ~default:false
        ~get:Kernel_function.is_entry_point;
      States.column model
        ~name:"defined"
        ~descr:(Md.plain "Is the function defined?")
        ~data:(module Data.Jbool)
        ~default:false
        ~get:Kernel_function.is_definition;
      States.column model
        ~name:"stdlib"
        ~descr:(Md.plain "Is the function from the Frama-C stdlib?")
        ~data:(module Data.Jbool)
        ~default:false
        ~get:is_stdlib;
      States.column model
        ~name:"builtin"
        ~descr:(Md.plain "Is the function a Frama-C builtin?")
        ~data:(module Data.Jbool)
        ~default:false
        ~get:is_builtin;
      States.column model
        ~name:"eva_analyzed"
        ~descr:(Md.plain "Has the function been analyzed by Eva")
        ~data:(module Data.Jbool)
        ~default:false
        ~get:is_eva_analyzed;
      States.column model
        ~name:"sloc"
        ~descr:(Md.plain "Source location")
        ~data:(module Position)
        ~get:(fun kf -> fst (Kernel_function.get_location kf));
      States.register_array model
        ~package ~key
        ~name:"functions"
        ~descr:(Md.plain "AST Functions")
        ~iter
        ~add_reload_hook:ast_update_hook
    end

end

(* -------------------------------------------------------------------------- *)
(* --- Marker Information                                                 --- *)
(* -------------------------------------------------------------------------- *)

module Information =
struct

  type info = {
    id: string;
    rank: int;
    label: string;
    title: string;
    enable: unit -> bool;
    pretty: Format.formatter -> Printer_tag.localizable -> unit
  }

  (* Info markers serialization *)

  module S =
  struct
    type t = (info * Jtext.t)
    let jtype = Package.(Jrecord[
        "id", Jstring ;
        "label", Jstring ;
        "title", Jstring ;
        "descr", Jtext.jtype ;
      ])
    let of_json _ = failwith "Information.Info"
    let to_json (info,text) = `Assoc [
        "id", `String info.id ;
        "label", `String info.label ;
        "title", `String info.title ;
        "descr", text ;
      ]
  end

  (* Info markers registry *)

  let rankId = ref 0
  let registry : (string,info) Hashtbl.t = Hashtbl.create 0

  let jtext pp marker =
    try
      let buffer = Jbuffer.create () in
      let fmt = Jbuffer.formatter buffer in
      pp fmt marker;
      Format.pp_print_flush fmt ();
      Jbuffer.contents buffer
    with Not_found ->
      `Null

  let rank ({rank},_) = rank
  let by_rank a b = Stdlib.compare (rank a) (rank b)

  let get_information tgt =
    let infos = ref [] in
    Hashtbl.iter
      (fun _ info ->
         if info.enable () then
           match tgt with
           | None -> infos := (info, `Null) :: !infos
           | Some marker ->
             let text = jtext info.pretty marker in
             if not (Jbuffer.is_empty text) then
               infos := (info, text) :: !infos
      ) registry ;
    List.sort by_rank !infos

  let signal = Request.signal ~package
      ~name:"getInformationUpdate"
      ~descr:(Md.plain "Updated AST information")

  let update () = Request.emit signal

  let register ~id ~label ~title ?(enable = fun _ -> true) pretty =
    let rank = incr rankId ; !rankId in
    let info = { id ; rank ; label ; title ; enable ; pretty } in
    if Hashtbl.mem registry id then
      ( let msg = Format.sprintf
            "Server.Kernel_ast.register_info: duplicate %S" id in
        raise (Invalid_argument msg) );
    Hashtbl.add registry id info

end

let () = Request.register ~package
    ~kind:`GET ~name:"getInformation"
    ~descr:(Md.plain
              "Get available information about markers. \
               When no marker is given, returns all kinds \
               of information (with empty `descr` field).")
    ~input:(module Joption(Marker))
    ~output:(module Jlist(Information.S))
    ~signals:[Information.signal]
    Information.get_information

(* -------------------------------------------------------------------------- *)
(* --- Default Kernel Information                                         --- *)
(* -------------------------------------------------------------------------- *)

let () = Information.register
    ~id:"kernel.ast.location"
    ~label:"Location"
    ~title:"Source file location"
    begin fun fmt loc ->
      let location = Printer_tag.loc_of_localizable loc in
      Filepath.pp_pos fmt (fst location)
    end

let () = Information.register
    ~id:"kernel.ast.varinfo"
    ~label:"Var"
    ~title:"Variable Information"
    begin fun fmt loc ->
      match loc with
      | PLval (_ , _, (Var x,NoOffset)) | PVDecl(_,_,x) ->
        if not x.vreferenced then Format.pp_print_string fmt "unused " ;
        begin
          match x.vstorage with
          | NoStorage -> ()
          | Extern -> Format.pp_print_string fmt "extern "
          | Static -> Format.pp_print_string fmt "static "
          | Register -> Format.pp_print_string fmt "register "
		  | Intrinsic -> Format.pp_print_string fmt "__intrinsic "
        end ;
        if x.vghost then Format.pp_print_string fmt "ghost " ;
        if x.vaddrof then Format.pp_print_string fmt "aliased " ;
        if x.vformal then Format.pp_print_string fmt "formal" else
        if x.vglob then Format.pp_print_string fmt "global" else
        if x.vtemp then Format.pp_print_string fmt "temporary" else
          Format.pp_print_string fmt "local" ;
      | _ -> raise Not_found
    end

let () = Information.register
    ~id:"kernel.ast.typeinfo"
    ~label:"Type"
    ~title:"Type of C/ASCL expression"
    begin fun fmt loc ->
      let open Printer in
      match loc with
      | PExp (_, _, e) -> pp_typ fmt (Cil.typeOf e)
      | PLval (_, _, lval) -> pp_typ fmt (Cil.typeOfLval lval)
      | PTermLval(_,_,_,lv) -> pp_logic_type fmt (Cil.typeOfTermLval lv)
      | PVDecl (_,_,vi) -> pp_typ fmt vi.vtype
      | _ -> raise Not_found
    end

(* -------------------------------------------------------------------------- *)
(* --- Marker at a position                                               --- *)
(* -------------------------------------------------------------------------- *)

let get_kf_marker (file, line, col) =
  let pos_path = Filepath.Normalized.of_string file in
  let pos =
    Filepath.{ pos_path; pos_lnum = line; pos_cnum = col; pos_bol = 0; }
  in
  let tag = Printer_tag.loc_to_localizable ~precise_col:true pos in
  let kf = Option.bind tag Printer_tag.kf_of_localizable in
  kf, tag

let () =
  let descr =
    Md.plain
      "Returns the marker and function at a source file position, if any. \
       Input: file path, line and column."
  in
  Request.register
    ~package ~descr ~kind:`GET ~name:"getMarkerAt"
    ~input:(module Jtriple (Jstring) (Jint) (Jint))
    ~output:(module Jpair (Joption (Kf)) (Joption (Marker)))
    get_kf_marker

(* -------------------------------------------------------------------------- *)
(* --- Files                                                              --- *)
(* -------------------------------------------------------------------------- *)

let get_files () =
  let files = Kernel.Files.get () in
  List.map (fun f -> (f:Filepath.Normalized.t:>string)) files

let () =
  Request.register
    ~package
    ~descr:(Md.plain "Get the currently analyzed source file names")
    ~kind:`GET
    ~name:"getFiles"
    ~input:(module Junit) ~output:(module Jlist(Jstring))
    get_files

let set_files files =
  let s = String.concat "," files in
  Kernel.Files.As_string.set s

let () =
  Request.register
    ~package
    ~descr:(Md.plain "Set the source file names to analyze.")
    ~kind:`SET
    ~name:"setFiles"
    ~input:(module Jlist(Jstring))
    ~output:(module Junit)
    set_files

(* -------------------------------------------------------------------------- *)
(* ----- Build a marker from an ACSL term ----------------------------------- *)
(* -------------------------------------------------------------------------- *)

type marker_term_input = { atStmt : stmt ; term : string }

module MarkerTermInput = struct
  type record
  let record : record Record.signature = Record.signature ()

  let atStmt =
    let descr = "The statement at which we will build the marker." in
    Record.field record ~name:"atStmt" ~descr:(Markdown.plain descr)
      (module Marker)

  let term =
    let descr = "The ACSL term." in
    Record.field record ~name:"term" ~descr:(Markdown.plain descr)
      (module Data.Jstring)

  let data =
    Record.publish record ~package ~name:"markerFromTermInput"
      ~descr:(Markdown.plain "<markerFromTerm> input")

  module R : Record.S with type r = record = (val data)
  type t = marker_term_input option
  let jtype = R.jtype

  let of_json js =
    let record = R.of_json js in
    match R.get atStmt record with
    | PStmt (_, s) | PStmtStart (_, s)
    | PLval (_, Kstmt s, _) | PExp (_, Kstmt s, _)
    | PTermLval (_, Kstmt s, _, _)
    | PVDecl (_, Kstmt s, _) ->
      let term = R.get term record in
      Some { atStmt = s ; term }
    | _ -> None

end

module MarkerTermOutput = Data.Joption (Marker)

let build_marker =
  Option.map @@ fun input ->
  let env = logic_environment () in
  let kf = Kernel_function.find_englobing_kf input.atStmt in
  let term = !Db.Properties.Interp.term ~env kf input.term in
  let key = (input.atStmt, term) in
  match Cache.find_opt cache key with
  | Some tag -> tag
  | None ->
    let exp = !Db.Properties.Interp.term_to_exp ~result:None term in
    let tag = Printer_tag.PExp (Some kf, Kstmt input.atStmt, exp) in
    Cache.add cache key tag ; tag

let descr = "Build a marker from an ACSL term."

let () = Request.register ~package
    ~kind:`GET ~name:"markerFromTerm" ~descr:(Markdown.plain descr)
    ~input:(module MarkerTermInput) ~output:(module MarkerTermOutput)
    build_marker

(**************************************************************************)
