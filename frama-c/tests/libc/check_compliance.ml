open Cil_types

let add_headers tbl id headers =
  try
    let old_headers = Hashtbl.find tbl id in
    Hashtbl.replace tbl id (old_headers @ headers)
  with Not_found ->
    Hashtbl.replace tbl id headers

class stdlib_visitor = object
  inherit Visitor.frama_c_inplace
  val in_stdlib = ref false
  val idents : (string, string list) Hashtbl.t = Hashtbl.create 500

  method! vglob_aux g =
    match Cil.findAttribute "fc_stdlib" (Cil.global_attributes g) with
    | [] ->
      in_stdlib := false;
      Cil.SkipChildren
    | attrparams ->
      let headers =
        Extlib.filter_map' (fun ap ->
            match ap with
            | AStr s -> s
            | _ -> assert false
          ) (Extlib.string_suffix ".h") attrparams
      in
      in_stdlib := true;
      begin
        match g with
        | GEnumTag ({eorig_name = id}, _loc) | GEnumTagDecl ({eorig_name = id}, _loc)
        | GCompTag ({corig_name = id}, _loc) | GCompTagDecl ({corig_name = id}, _loc)
        | GVar ({vorig_name = id}, _, _loc) | GVarDecl ({vorig_name = id}, _loc)
        | GFunDecl (_, {vorig_name = id}, _loc)
        | GFun ({svar = {vorig_name = id}}, _loc) ->
          add_headers idents id headers
        | _ -> ()
      end;
      Cil.DoChildren

  method get_idents = idents
end

let run_once = ref false

module StringSet = Set.Make(String)

module Json =
struct
  open Yojson.Basic
  open Util

  let parse dir f =
    let file = Filename.concat dir f in
    Kernel.feedback "Parsing %s" f;
    let json = Yojson.Basic.from_file file in
    member "data" json

  let to_set (json : t) : StringSet.t =
    json |> to_list |> List.map to_string |> StringSet.of_list

  let keys (json : t) : StringSet.t =
    json |> to_assoc |> List.map fst |> StringSet.of_list

  type _ table_format =
    | HeadersOnly : string table_format
    | HeadersAndExtensions : (string*t list) table_format

  let to_table : type a. a table_format -> t -> (string,a) Hashtbl.t =
    let convert json : a table_format -> a = function
      | HeadersOnly ->
        json |> member "header" |> to_string
      | HeadersAndExtensions ->
        json |> member "header" |> to_string,
        json |> member "extensions" |> to_list
    in
    fun format json ->
      let table = Hashtbl.create 500 in
      json |> to_assoc |> List.iter (fun (ident, values) ->
        Hashtbl.replace table ident (convert values format));
      table
end

let ident_to_be_ignored id headers =
  Extlib.string_prefix "__" id ||
  Extlib.string_prefix "Frama_C" id ||
  List.filter (fun h -> not (Extlib.string_prefix "__fc" h)) headers = []

let check_ident c11 posix glibc nonstandard c11_headers id headers =
  if ident_to_be_ignored id headers then (* nothing to check *) ()
  else begin
    if Hashtbl.mem c11 id then begin
      (* Check that the header is the expected one.
         Note that some symbols may appear in more than one header,
         possibly due to collisions
         e.g. 'flock' as type and function). *)
      let h = Hashtbl.find c11 id in
      if not (StringSet.mem h c11_headers) then
        Kernel.warning "<%a>:%s : C11 says %s"
          (Pretty_utils.pp_list ~sep:"," Format.pp_print_string) headers
          id h
    end
    else if Hashtbl.mem posix id then begin
      (* check that the header is the expected one *)
      let (h, _) = Hashtbl.find posix id in
      (* arpa/inet.h and netinet/in.h are special cases: due to mutual
         inclusion, there are always issues with their symbols;
         also, timezone is a special case, since it is a type in
         sys/time.h, but a variable in time.h in POSIX. However, its
         declaration as extern is erased by rmtmps, since it is
         unused. *)
      if not (List.mem h headers) &&
         not (List.mem "arpa/inet.h" headers && h = "netinet/in.h" ||
              List.mem "netinet/in.h" headers && h = "arpa/inet.h") &&
         id <> "timezone"
      then
        Kernel.warning "<%a>:%s : POSIX says %s"
          (Pretty_utils.pp_list ~sep:"," Format.pp_print_string) headers
          id h
    end
    else if not (StringSet.(mem id glibc || mem id nonstandard)) then
      Kernel.warning "<%a>:%s : unknown identifier"
        (Pretty_utils.pp_list ~sep:"," Format.pp_print_string) headers
        id
  end

let () =
  Db.Main.extend (fun () ->
      if not !run_once then begin
        run_once := true;
        let vis = new stdlib_visitor in
        ignore (Visitor.visitFramacFile (vis :> Visitor.frama_c_visitor) (Ast.get ()));
        let fc_stdlib_idents = vis#get_idents in
        let dir = Filename.concat (Fc_config.datadir:>string) "compliance" in
        let c11_idents = Json.(to_table HeadersOnly (parse dir "c11_functions.json"))
        and c11_headers = Json.(to_set (parse dir "c11_headers.json"))
        and glibc_idents = Json.(to_set (parse dir "glibc_functions.json"))
        and posix_idents = Json.(to_table HeadersAndExtensions (parse dir "posix_identifiers.json"))
        and nonstandard_idents = Json.(keys (parse dir "nonstandard_identifiers.json")) in
        let check_ident_fun = check_ident c11_idents posix_idents glibc_idents nonstandard_idents c11_headers in
        Hashtbl.iter check_ident_fun fc_stdlib_idents
      end)
