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
(* --- Server Documentation                                               --- *)
(* -------------------------------------------------------------------------- *)

open Package
type json = Yojson.Basic.t
module Md = Markdown
module Senv = Server_parameters
module Pages = Map.Make(String)

type chapter = [ `Protocol | `Kernel | `Plugin of string ]

(* Section contents can be generated statically or dynamically.
   Typically, general kernel dictionary entries can be extended by plugins.
   The general case is to have a function that builds the (final) content
   on demand. *)
type section = (unit -> Markdown.elements)

type page = {
  path : string ;
  rootdir : string ; (* path to document root *)
  chapter : chapter ;
  title : string ;
  order : int ;
  descr : Markdown.elements ;
  readme: string option ;
  mutable sections : section list ;
}

let order = ref 0
let pages : page Pages.t ref = ref Pages.empty
let plugins : string list ref = ref []
let entries : (string * Markdown.href) list ref = ref []
let path page = page.path
let href page name : Markdown.href = Section( page.path , name )

(* -------------------------------------------------------------------------- *)
(* --- Page Collection                                                    --- *)
(* -------------------------------------------------------------------------- *)

let chapter pg = pg.chapter

let path_for chapter filename =
  match chapter with
  | `Protocol -> "." , filename
  | `Kernel -> ".." , Printf.sprintf "kernel/%s" filename
  | `Plugin name -> "../.." , Printf.sprintf "plugins/%s/%s" name filename

let page chapter ~title ?(descr=[]) ?readme ~filename () =
  let rootdir , path = path_for chapter filename in
  try
    let other = Pages.find path !pages in
    Senv.failure "Duplicate page '%s' path@." path ; other
  with Not_found ->
    let order = incr order ; !order in
    let page = {
      order ; rootdir ; path ;
      chapter ; title ; descr ; readme ;
      sections=[] ;
    } in
    pages := Pages.add path page !pages ; page

let static () = []

let publish ~page ?name ?(index=[]) ~title
    ?(contents=[])
    ?(generated=static)
    () =
  let id = match name with Some id -> id | None -> title in
  let href = Md.Section( page.path , id ) in
  let section () = Markdown.section ?name ~title (contents @ generated ()) in
  List.iter (fun entry -> entries := (entry , href) :: !entries) index ;
  page.sections <- section :: page.sections ; href

let protocole ~title ~readme:filename =
  let readme = Printf.sprintf "%s/server/%s" (Fc_config.datadir :> string) filename in
  ignore (page `Protocol ~title ~readme ~filename ())

let () = protocole ~title:"Architecture" ~readme:"server.md"

(* -------------------------------------------------------------------------- *)
(* --- Package Publication                                                --- *)
(* -------------------------------------------------------------------------- *)

let href_of_ident names id =
  let chapter = match id.plugin with
    | Kernel -> `Kernel | Plugin p -> `Plugin p in
  let filename = String.concat "_" id.package ^ ".md" in
  let page = snd @@ path_for chapter filename in
  let text = try IdMap.find id names with Not_found -> id.name in
  Md.link ~text:(Md.code text) ~page ~name:id.name ()

let page_of_package pkg =
  let chapter = match pkg.p_plugin with
    | Kernel -> `Kernel | Plugin p -> `Plugin p in
  let filename = String.concat "_" pkg.p_package ^ ".md" in
  try
    let _,path = path_for chapter filename in
    Pages.find path !pages
  with Not_found ->
    page chapter
      ~title:pkg.p_title
      ~descr:(Markdown.par pkg.p_descr)
      ?readme:pkg.p_readme
      ~filename ()

let kind_of_decl = function
  | D_signal -> "SIGNAL"
  | D_value _ | D_state _ -> "STATE"
  | D_array _ -> "ARRAY"
  | D_type _ | D_record _ | D_enum _ -> "DATA"
  | D_request { rq_kind=`GET } -> "GET"
  | D_request { rq_kind=`SET } -> "SET"
  | D_request { rq_kind=`EXEC } -> "EXEC"
  | D_loose _ | D_safe _ | D_order _ -> assert false

let pp_for ?decl names =
  let self =
    match decl with
    | Some d ->
      let name = d.d_ident.name in
      Md.link ~text:(Md.code name) ~name ()
    | None ->
      Md.code "self"
  in Package.{ self ; ident = href_of_ident names }

let md_param ~kind pp prm =
  Md.emph kind @ Md.code "::=" @ match prm with
  | P_value jt -> Package.md_jtype pp jt
  | P_named _ -> Md.code "{" @ Md.emph (kind ^ "…") @ Md.code "}"

let md_named ~kind pp = function
  | P_value _ -> []
  | P_named prms ->
    let title = String.capitalize_ascii kind in
    Md.table (Package.md_fields ~title pp prms)

let md_signals signals =
  if signals = [] then []
  else
    Md.quote (Md.emph "signals") @
    Md.block Md.(list (List.map (fun x -> text (code x)) signals))

let descr_of_decl names decl =
  match decl.d_kind with
  | D_safe _ | D_loose _  | D_order _ -> assert false
  | D_signal -> []
  | D_state _ -> [] (* TBC *)
  | D_value _ -> [] (* TBC *)
  | D_array _ -> [] (* TBC *)
  | D_type data ->
    let pp = pp_for ~decl names in
    Md.quote (pp.self @ Md.code "::=" @ Package.md_jtype pp data)
  | D_record fields ->
    let pp = pp_for ~decl names in
    Md.quote (pp.self @ Md.code "::= {" @ Md.emph "fields…" @ Md.code "}") @
    Md.table (Package.md_fields pp fields)
  | D_enum tags ->
    let pp = pp_for ~decl names in
    Md.quote (pp.self @ Md.code "::=" @ Md.emph "tags…") @
    Md.table (Package.md_tags tags)
  | D_request rq ->
    let pp = pp_for names in
    Md.quote (md_param ~kind:"input" pp rq.rq_input) @
    Md.quote (md_param ~kind:"output" pp rq.rq_output) @
    md_named ~kind:"input" pp rq.rq_input @
    md_named ~kind:"output" pp rq.rq_output @
    md_signals rq.rq_signals

let declaration page names decl =
  match decl.d_kind with
  | D_safe _ | D_loose _ | D_order _ -> ()
  | _ ->
    let name = decl.d_ident.name in
    let fullname = name_of_ident decl.d_ident in
    let kind = kind_of_decl decl.d_kind in
    (* let title = Printf.sprintf "`%s` %s" kind fullname in *)
    let title = Printf.sprintf "%s (`%s`)" fullname kind in
    let index = [ title ] in
    let contents = Markdown.par decl.d_descr in
    let generated () = descr_of_decl names decl in
    let href = publish ~page ~name ~title ~index ~contents ~generated () in
    ignore href

let package pkg =
  begin
    let page = page_of_package pkg in
    let names = Package.resolve pkg in
    List.iter (declaration page names) pkg.p_content ;
  end

(* -------------------------------------------------------------------------- *)
(* --- Tables of Content                                                  --- *)
(* -------------------------------------------------------------------------- *)

let title_of_chapter = function
  | `Protocol -> "Protocols"
  | `Kernel -> "Kernel"
  | `Plugin name -> "Plugin " ^ String.capitalize_ascii name

let pages_of_chapter c =
  let w = ref [] in
  Pages.iter
    (fun _ p -> if p.chapter = c then w := p :: !w) !pages ;
  List.sort (fun p q -> p.order - q.order) !w

let table_of_page p =
  Md.text (Md.link ~text:(Md.plain p.title) ~page:p.path ())

let table_of_chapter c =
  [Md.H2 (Markdown.plain (title_of_chapter c), None);
   Md.Block (Md.list (List.map table_of_page (pages_of_chapter c)))]

let table_of_contents () =
  table_of_chapter `Protocol @
  table_of_chapter `Kernel @
  List.concat
    (List.map
       (fun p -> table_of_chapter (`Plugin p))
       (List.sort String.compare !plugins))

module Cmap = Map.Make
    (struct
      type t = string list
      let compare = Stdlib.compare
    end)

let index_entry (title,href) =
  Md.text @@ Markdown.href ~text:(Md.plain title) href

let index () =
  let category name =
    match List.rev (String.split_on_char '.' name) with
    | [] -> []
    | _::rpath -> List.rev rpath in
  let cmap =
    List.fold_left
      (fun cs entry ->
         let c = category (fst entry) in
         let es = try Cmap.find c cs with Not_found -> [] in
         Cmap.add c (entry :: es) cs)
      Cmap.empty !entries in
  let by_name (a,_) (b,_) = String.compare a b in
  let categories = Cmap.fold
      (fun c es ces -> ( c , List.sort by_name es ) :: ces)
      cmap [] in
  begin
    List.fold_left
      (fun elements (c,es) ->
         let entries =
           Md.Block (Md.list @@ List.map index_entry es) :: elements in
         if c = [] then entries
         else
           let cname = String.concat "." c in
           let title = Printf.sprintf "Index of `%s`" cname in
           Md.H3(Md.plain title,None) :: entries
      ) [] categories
  end

let link ~toc ~title ~href : json =
  let link = [ "title" , `String title ; "href" , `String href ] in
  `Assoc (if not toc then link else ( "toc" , `Bool true ) ::  link)

let link_page page : json list =
  List.fold_right
    (fun p links ->
       if p.chapter = page.chapter then
         let toc = (p.path = page.path) in
         let href = Filename.basename p.path in
         link ~toc ~title:p.title ~href :: links
       else links
    ) (pages_of_chapter page.chapter) []

let maindata : json =
  `Assoc [
    "document", `String "Frama-C Server" ;
    "title",`String "Presentation" ;
    "root", `String "." ;
  ]

let metadata page : json =
  `Assoc [
    "document", `String "Frama-C Server" ;
    "chapter", `String (title_of_chapter page.chapter) ;
    "title", `String page.title ;
    "root", `String page.rootdir ;
    "link",`List (link_page page) ;
  ]

(* -------------------------------------------------------------------------- *)
(* --- Dump Documentation                                                 --- *)
(* -------------------------------------------------------------------------- *)

let pp_one_page ~root ~page ~title body =
  let full_path = Filepath.Normalized.concat root page in
  let dir = Filename.dirname (full_path:>string) in
  if not (Sys.file_exists dir) then Extlib.mkdir ~parents:true dir 0o755;
  try
    let chan = open_out (full_path:>string) in
    let fmt = Format.formatter_of_out_channel chan in
    let title = Md.plain title in
    Markdown.(pp_pandoc ~page fmt (pandoc ~title body))
  with Sys_error e ->
    Senv.fatal "Could not open file %a for writing: %s"
      Filepath.Normalized.pretty full_path e

(* Build section contents in reverse order *)
let build d s = List.fold_left (fun d s -> s() :: d) d s

let dump ~root ?(meta=true) () =
  begin
    Pages.iter
      (fun path page ->
         Senv.feedback "[doc] Page: '%s'" path ;
         let title = page.title in
         let intro = match page.readme with
           | None -> Markdown.section ~title page.descr
           | Some file ->
             if Sys.file_exists file
             then Markdown.rawfile file @ page.descr
             else (Senv.warning "Can not find %S file" file ;
                   Markdown.section ~title page.descr)
         in
         let body = Markdown.subsections page.descr (build [] page.sections) in
         pp_one_page ~root ~page:path ~title (intro @ body) ;
         if meta then
           let path = Filepath.Normalized.concat root (path ^ ".json") in
           Yojson.Basic.to_file (path:>string) (metadata page) ;
      ) !pages ;
    Senv.feedback "[doc] Page: 'readme.md'" ;
    if meta then
      let path = Filepath.Normalized.concat root "readme.md.json" in
      Yojson.Basic.to_file (path:>string) maindata ;
      let body =
        [ Md.H1 (Md.plain "Presentation", None);
          Md.Block (Md.text (Md.format "Version %s" Fc_config.version))]
        @
        table_of_contents ()
        @
        [Md.H2 (Md.plain "Index", None)]
        @
        index ()
      in
      let title = "Presentation" in
      pp_one_page ~root ~page:"readme.md" ~title body
  end

let () =
  Db.Main.extend begin
    fun () ->
      if not (Senv.Doc.is_empty ()) then
        let root = Senv.Doc.get () in
        if Sys.is_directory (root:>string) then
          begin
            Senv.feedback "[doc] Root: '%a'" Filepath.Normalized.pretty root ;
            Package.iter package ;
            dump ~root () ;
          end
        else
          Senv.error "[doc] File '%a' is not a directory"
            Filepath.Normalized.pretty root
  end

(* -------------------------------------------------------------------------- *)
