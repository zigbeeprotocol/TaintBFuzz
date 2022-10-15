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
(* --- Frama-C TypeScript API Generator                                   --- *)
(* -------------------------------------------------------------------------- *)

module Self = Plugin.Register
  (struct
    let name = "Server TypeScript API"
    let shortname = "server-tsc"
    let help = "Generate TypeScript API for Server"
  end)

module TSC = Self.Action
    (struct
      let option_name = "-server-tsc"
      let help = "Generate TypeScript API"
    end)

module OUT = Self.String
    (struct
      let option_name = "-server-tsc-out"
      let arg_name = "path"
      let default = "src"
      let help = Printf.sprintf "Output directory (default is '%s')" default
    end)

module Md = Markdown
module Pkg = Server.Package

(* -------------------------------------------------------------------------- *)
(* --- TS Utils                                                           --- *)
(* -------------------------------------------------------------------------- *)

let keywords = [
  "break"; "case"; "catch"; "class"; "const"; "continue"; "debugger";
  "default"; "delete"; "do"; "else"; "enum"; "export"; "extends"; "false";
  "finally"; "for"; "function"; "if"; "import"; "in"; "instanceof"; "new";
  "null"; "return"; "super"; "switch"; "this"; "throw"; "true"; "try";
  "typeof"; "var"; "void"; "while"; "with"; "as"; "implements"; "interface";
  "let"; "package"; "private"; "protected"; "public"; "static"; "yield"; "any";
  "boolean"; "constructor"; "declare"; "get"; "module"; "require"; "number";
  "set"; "string"; "symbol"; "type"; "from"; "of";
  "Json"; "Compare"; "Server"; "State";
]

let pp_descr = Md.pp_text ?page:None

let name_of_kind = function
  | `GET -> "GET"
  | `SET -> "SET"
  | `EXEC -> "EXEC"

let makeDescr ?(indent="") fmt descr =
  if descr <> [] then
    Format.fprintf fmt "%s/** @[<hov 0>%a@] */@." indent pp_descr descr

let getSelf = function
  | None -> Self.fatal "Unexpected recursive type"
  | Some id -> id

(* -------------------------------------------------------------------------- *)
(* --- Jtype Generator                                                    --- *)
(* -------------------------------------------------------------------------- *)

let makeJtype ?self ~names =
  let open Pkg in
  let pp_ident fmt id =
    match IdMap.find id names with
    | name -> Format.pp_print_string fmt name
    | exception Not_found -> Self.abort "Undefined '%a'" pp_ident id in
  let rec pp fmt = function
    | Jany -> Format.pp_print_string fmt "Json.json"
    | Jself -> Format.pp_print_string fmt (getSelf self).name
    | Jnull -> Format.pp_print_string fmt "null"
    | Jnumber -> Format.pp_print_string fmt "number"
    | Jboolean -> Format.pp_print_string fmt "boolean"
    | Jstring | Jalpha -> Format.pp_print_string fmt "string"
    | Jtag a -> Format.fprintf fmt "\"%s\"" a
    | Jkey kd -> Format.fprintf fmt "Json.key<'#%s'>" kd
    | Jindex kd -> Format.fprintf fmt "Json.index<'#%s'>" kd
    | Jdict js -> Format.fprintf fmt "@[<hov 2>Json.dict<@,%a>@]" pp js
    | Jdata id | Jenum id -> pp_ident fmt id
    | Joption js -> Format.fprintf fmt "%a |@ undefined" pp js
    | Jtuple js ->
      Pretty_utils.pp_list ~pre:"@[<hov 2>[ " ~sep:",@ " ~suf:"@ ]@]" pp fmt js
    | Junion js ->
      Pretty_utils.pp_list ~pre:"@[<hov 0>" ~sep:" |@ " ~suf:"@]" protect fmt js
    | Jrecord fjs ->
      Pretty_utils.pp_list ~pre:"@[<hov 2>{ " ~sep:",@ " ~suf:"@ }@]" field fmt fjs
    | Jarray js | Jlist js -> Format.fprintf fmt "%a[]" protect js
  and protect fmt js = match js with
    | Junion _ | Joption _ -> Format.fprintf fmt "@[<hov 2>(%a)@]" pp js
    | _ -> pp fmt js
  and field fmt (fd,js) =
    match js with
    | Joption js ->
      Format.fprintf fmt "@[<hov 4>%s?:@ %a@]" fd pp js
    | _ ->
      Format.fprintf fmt "@[<hov 4>%s:@ %a@]" fd pp js
  in pp

(* -------------------------------------------------------------------------- *)
(* --- Jtype Decoder                                                      --- *)
(* -------------------------------------------------------------------------- *)

let jprim fmt name = Format.fprintf fmt "Json.%s" name
let jkey fmt kd = Format.fprintf fmt "Json.jKey<'#%s'>('#%s')" kd kd
let jindex fmt kd = Format.fprintf fmt "Json.jIndex<'#%s'>('#%s')" kd kd

let jcall names fmt id =
  try Format.pp_print_string fmt (Pkg.IdMap.find id names)
  with Not_found -> Self.abort "Undefined identifier '%a'" Pkg.pp_ident id

let jsafe ~safe msg pp fmt d =
  if safe then
    Format.fprintf fmt "@[<hov 2>Json.jFail(@,%a,@,'%s expected')@]" pp d msg
  else
    pp fmt d

let jtry ~safe pp fmt d =
  if safe then
    pp fmt d
  else
    Format.fprintf fmt "@[<hov 2>Json.jTry(@,%a)@]" pp d

let jenum names fmt id = Format.fprintf fmt "Json.jEnum(%a)" (jcall names) id

let junion ~jtype ~makeLoose fmt jts =
  begin
    Format.fprintf fmt "@[<hv 0>@[<hv 2>Json.jUnion<%a>("
      jtype (Pkg.Junion jts) ;
    List.iter
      (fun js -> Format.fprintf fmt "@ @[<hov 2>%a@]," makeLoose js) jts ;
    Format.fprintf fmt "@]@,)@]" ;
  end

let jrecord ~makeSafe fmt jts =
  begin
    Format.fprintf fmt "@[<hv 0>@[<hv 2>Json.jObject({" ;
    List.iter
      (fun (fd,js) ->
         Format.fprintf fmt "@ @[<hov 2>%s: %a@]," fd makeSafe js) jts ;
    Format.fprintf fmt "@]@,})@]" ;
  end

let jtuple ~makeSafe fmt jts =
  begin
    let name = match List.length jts with
      | 2 -> "jPair"
      | 3 -> "jTriple"
      | 4 -> "jTuple4"
      | 5 -> "jTuple5"
      | n -> Self.fatal "No jTuple%d defined" n
    in
    Format.fprintf fmt "@[<hv 0>@[<hv 2>Json.%s(" name ;
    List.iter
      (fun js -> Format.fprintf fmt "@ @[<hov 2>%a@]," makeSafe js) jts ;
    Format.fprintf fmt "@]@,)@]" ;
  end

let rec makeDecoder ~safe ?self ~names fmt js =
  let open Pkg in
  let makeSafe = makeDecoder ?self ~names ~safe:true in
  let makeLoose = makeDecoder ?self ~names ~safe:false in
  match js with
  | Jany -> jprim fmt "jAny"
  | Jnull -> jprim fmt "jNull"
  | Jboolean -> jsafe ~safe "Boolean" jprim fmt "jBoolean"
  | Jnumber -> jsafe ~safe "Number" jprim fmt "jNumber"
  | Jstring | Jalpha -> jsafe ~safe "String" jprim fmt "jString"
  | Jtag a -> Format.fprintf fmt "Json.jTag(\"%s\")" a
  | Jkey kd -> jsafe ~safe ("#" ^ kd) jkey fmt kd
  | Jindex kd -> jsafe ~safe ("#" ^ kd) jindex fmt kd
  | Jdata id -> jcall names fmt (Pkg.Derived.decode ~safe id)
  | Jenum id -> jsafe ~safe (Pkg.name_of_ident id) (jenum names) fmt id
  | Jself -> jcall names fmt (Pkg.Derived.decode ~safe (getSelf self))
  | Joption js -> makeLoose fmt js
  | Jdict js ->
    Format.fprintf fmt "@[<hov 2>Json.jDict(@,%a)@]" makeLoose js
  | Jlist js ->
    Format.fprintf fmt "@[<hov 2>Json.jList(@,%a)@]" makeLoose js
  | Jarray js ->
    if safe
    then Format.fprintf fmt "@[<hov 2>Json.jArray(%a)@]" makeSafe js
    else Format.fprintf fmt "@[<hov 2>Json.jTry(jArray(%a))@]" makeSafe js
  | Junion jts ->
    let jtype = makeJtype ?self ~names in
    jsafe ~safe "Union" (junion ~jtype ~makeLoose) fmt jts
  | Jrecord jfs -> jsafe ~safe "Record" (jrecord ~makeSafe) fmt jfs
  | Jtuple jts -> jtry ~safe (jtuple ~makeSafe) fmt jts

let makeLooseNeedSafe = function
  | Pkg.Jtuple _ | Pkg.Jarray _ -> true
  | _ -> false

let makeRootDecoder ~safe ~self ~names fmt js =
  let open Pkg in
  match js with
  | Joption _ | Jdict _ | Jlist _ when safe ->
    jcall names fmt (Pkg.Derived.loose self)
  | Jtuple _ | Jarray _ when not safe ->
    Format.fprintf fmt "Json.jTry(%a)"
      (jcall names) (Pkg.Derived.safe self)
  | Junion _ | Jrecord _ when safe ->
    Format.fprintf fmt "Json.jFail(%a,'%s expected')"
      (jcall names) (Pkg.Derived.loose self)
      (String.capitalize_ascii self.name)
  | _ -> makeDecoder ~safe ~self ~names fmt js

(* -------------------------------------------------------------------------- *)
(* --- Parameter Decoder                                                  --- *)
(* -------------------------------------------------------------------------- *)

let typeOfParam = function
  | Pkg.P_value js -> js
  | Pkg.P_named fjs -> Jrecord (List.map Pkg.field fjs)

(* -------------------------------------------------------------------------- *)
(* --- Jtype Order                                                        --- *)
(* -------------------------------------------------------------------------- *)

let makeOrder ~self ~names fmt js =
  let open Pkg in
  let rec pp fmt = function
    | Jnull -> Format.pp_print_string fmt "Compare.equal"
    | Jalpha -> Format.pp_print_string fmt "Compare.alpha"
    | Jnumber | Jindex _ -> Format.pp_print_string fmt "Compare.number"
    | Jstring | Jkey _ -> Format.pp_print_string fmt "Compare.string"
    | Jboolean -> Format.pp_print_string fmt "Compare.boolean"
    | Jself -> jcall names fmt (Pkg.Derived.order self)
    | Jdata id -> jcall names fmt (Pkg.Derived.order id)
    | Joption js ->
      Format.fprintf fmt "@[<hov 2>Compare.defined(@,%a)@]" pp js
    | Jenum id ->
      Format.fprintf fmt "@[<hov 2>Compare.byEnum(@,%a)@]" (jcall names) id
    | Jlist js | Jarray js ->
      Format.fprintf fmt "@[<hov 2>Compare.array(@,%a)@]" pp js
    | Jtuple jts ->
      let name = match List.length jts with
        | 2 -> "pair"
        | 3 -> "triple"
        | 4 -> "tuple4"
        | 5 -> "tuple5"
        | n -> Self.abort "No comparison for %d-tuples" n in
      Format.fprintf fmt "@[<hv 0>@[<hv 2>Compare.%s(" name ;
      List.iter (fun js -> Format.fprintf fmt "@,%a," pp js) jts ;
      Format.fprintf fmt "@]@,)@]" ;
    | Jrecord jfs ->
      Format.fprintf fmt "@[<hv 0>@[<hv 2>Compare.byFields@,<%a>({"
        (makeJtype ~self ~names) (Jrecord jfs) ;
      List.iter
        (fun (fd,js) -> Format.fprintf fmt "@ @[<hov 2>%s: %a,@]" fd pp js) jfs ;
      Format.fprintf fmt "@]@ })@]" ;
    | Jdict js ->
      let jtype fmt js = makeJtype ~names fmt js in
      Format.fprintf fmt
        "@[<hov 2>Compare.dictionary<@,Json.dict<%a>>(@,%a)@]"
        jtype js pp js
    | Jany | Junion _ | Jtag _ ->
      Format.fprintf fmt "Compare.structural"
  in pp fmt js

(* -------------------------------------------------------------------------- *)
(* --- Declaration Generator                                              --- *)
(* -------------------------------------------------------------------------- *)

let makeRecursive fn fmt js =
  if Pkg.isRecursive js then
    Format.fprintf fmt "(_x: any) => %a(_x)" fn js
  else fn fmt js

let makeRecursive2 fn fmt js =
  if Pkg.isRecursive js then
    Format.fprintf fmt "(_x: any, _y: any) => %a(_x,_y)" fn js
  else fn fmt js

let makeDeclaration fmt names d =
  let open Pkg in
  Format.pp_print_newline fmt () ;
  let self = d.d_ident in
  let jtype = makeJtype ~self ~names in
  match d.d_kind with

  | D_type js ->
    makeDescr fmt d.d_descr ;
    Format.fprintf fmt "@[<hv 2>export type %s =@ %a;@]@\n" self.name jtype js

  | D_record fjs ->
    makeDescr fmt d.d_descr ;
    Format.fprintf fmt "export interface %s {@\n" self.name ;
    List.iter
      (fun { fd_name = fd ; fd_type = js ; fd_descr = doc } ->
         makeDescr ~indent:"  " fmt doc ;
         match js with
         | Joption js ->
           Format.fprintf fmt "  @[<hov 2>%s?: %a;@]@\n" fd jtype js
         | _ ->
           Format.fprintf fmt "  @[<hov 2>%s: %a;@]@\n" fd jtype js
      ) fjs ;
    Format.fprintf fmt "}@\n"

  | D_enum tgs ->
    makeDescr fmt d.d_descr ;
    Format.fprintf fmt "export enum %s {@\n" self.name ;
    List.iter
      (fun { tg_name = tag ; tg_descr = doc } ->
         makeDescr ~indent:"  " fmt doc ;
         Format.fprintf fmt "  %s = '%s',@\n" tag tag ;
      ) tgs ;
    Format.fprintf fmt "}@\n"

  | D_signal ->
    makeDescr fmt d.d_descr ;
    Format.fprintf fmt "export const %s: Server.Signal = {@\n" self.name ;
    Format.fprintf fmt "  name: '%s',@\n" (Pkg.name_of_ident d.d_ident) ;
    Format.fprintf fmt "};@\n"

  | D_request rq ->
    let kind = name_of_kind rq.rq_kind in
    let prefix = String.capitalize_ascii (String.lowercase_ascii kind) in
    let input = typeOfParam rq.rq_input in
    let output = typeOfParam rq.rq_output in
    let makeParam fmt js = makeDecoder ~safe:false ~names fmt js in
    Format.fprintf fmt
      "@[<hv 2>const %s_internal: Server.%sRequest<@,%a,@,%a@,>@] = {@\n"
      self.name prefix jtype input jtype output ;
    Format.fprintf fmt "  kind: Server.RqKind.%s,@\n" kind ;
    Format.fprintf fmt "  name:   '%s',@\n" (Pkg.name_of_ident d.d_ident) ;
    Format.fprintf fmt "  input:  %a,@\n" makeParam input ;
    Format.fprintf fmt "  output: %a,@\n" makeParam output ;
    Format.fprintf fmt "  signals: %a,@\n"
      (Pretty_utils.pp_list
         ~empty:"[]" ~pre:"@[<hov 2>[ " ~sep:",@ " ~suf:"@ ]@]"
         (fun fmt s -> Format.fprintf fmt "{ name: '%s' }" s))
         rq.rq_signals;
    Format.fprintf fmt "};@\n" ;
    makeDescr fmt d.d_descr ;
    Format.fprintf fmt
      "@[<hv 2>export const %s: Server.%sRequest<@,%a,@,%a@,>@]\
       = %s_internal;@\n"
      self.name prefix jtype input jtype output self.name ;

  | D_value js ->
    Format.fprintf fmt
      "@[<hv 2>const %s_internal: State.Value<@,%a@,>@] = {\n"
      self.name jtype js ;
    Format.fprintf fmt "  name: '%s',@\n" (Pkg.name_of_ident self) ;
    Format.fprintf fmt "  signal: %a,@\n"
      (jcall names) (Pkg.Derived.signal self) ;
    Format.fprintf fmt "  getter: %a,@\n"
      (jcall names) (Pkg.Derived.getter self) ;
    Format.fprintf fmt "};@\n" ;
    makeDescr fmt d.d_descr ;
    Format.fprintf fmt
      "@[<hv 2>export const %s: State.Value<@,%a@,>@] = %s_internal;\n"
      self.name jtype js self.name ;

  | D_state js ->
    Format.fprintf fmt
      "@[<hv 2>const %s_internal: State.State<@,%a@,>@] = {@\n"
      self.name jtype js ;
    Format.fprintf fmt "  name: '%s',@\n" (Pkg.name_of_ident self) ;
    Format.fprintf fmt "  signal: %a,@\n"
      (jcall names) (Pkg.Derived.signal self) ;
    Format.fprintf fmt "  getter: %a,@\n"
      (jcall names) (Pkg.Derived.getter self) ;
    Format.fprintf fmt "  setter: %a,@\n"
      (jcall names) (Pkg.Derived.setter self) ;
    Format.fprintf fmt "};@\n" ;
    makeDescr fmt d.d_descr ;
    Format.fprintf fmt
      "@[<hv 2>export const %s: State.State<@,%a@,>@] = %s_internal;@\n"
      self.name jtype js self.name;


  | D_array { arr_key ; arr_kind = jkey } ->
    let data = Pkg.Derived.data self in
    let jrow = Pkg.Jdata data in
    Format.fprintf fmt
      "@[<hv 2>const %s_internal: State.Array<@,%a,@,%a@,>@] = {@\n"
      self.name jtype jkey jtype jrow ;
    Format.fprintf fmt "  name: '%s',@\n" (Pkg.name_of_ident self) ;
    Format.fprintf fmt "  getkey: ((d:%a) => d.%s),@\n" jtype jrow arr_key ;
    Format.fprintf fmt "  signal: %a,@\n"
      (jcall names) (Pkg.Derived.signal self) ;
    Format.fprintf fmt "  fetch: %a,@\n"
      (jcall names) (Pkg.Derived.fetch self) ;
    Format.fprintf fmt "  reload: %a,@\n"
      (jcall names) (Pkg.Derived.reload self) ;
    Format.fprintf fmt "  order: %a,@\n"
      (jcall names) (Pkg.Derived.order data) ;
    Format.fprintf fmt "};@\n" ;
    makeDescr fmt d.d_descr ;
    Format.fprintf fmt
      "@[<hv 2>export const %s: State.Array<@,%a,@,%a@,>@] = %s_internal;@\n"
      self.name jtype jkey jtype jrow self.name ;

  | D_safe(id,js) ->
    makeDescr fmt d.d_descr ;
    Format.fprintf fmt
      "@[<hov 2>@[<hv 0>export const %s: Json.Safe<@,%a@,>@] =@ %a;@]\n"
      self.name (jcall names) id
      (makeRecursive (makeRootDecoder ~safe:true ~self:id ~names)) js

  | D_loose(id,js) ->
    makeDescr fmt d.d_descr ;
    Format.fprintf fmt
      "@[<hov 2>@[<hv 0>export const %s: Json.Loose<@,%a@,>@] =@ %a;@]\n"
      self.name (jcall names) id
      (makeRecursive (makeRootDecoder ~safe:false ~self:id ~names)) js

  | D_order(id,js) ->
    makeDescr fmt d.d_descr ;
    Format.fprintf fmt
      "@[<hov 2>@[<hv 0>export const %s: Compare.Order<@,%a@,>@] =@ %a;@]\n"
      self.name (jcall names) id
      (makeRecursive2 (makeOrder ~self:id ~names)) js

(* -------------------------------------------------------------------------- *)
(* --- Declaration Ranking                                                --- *)
(* -------------------------------------------------------------------------- *)

type ranking = {
  mutable rank : int ;
  mutable mark : int Pkg.IdMap.t ;
  index : Pkg.declInfo Pkg.IdMap.t ;
}

let depends d =
  match d.Pkg.d_kind with
  | D_loose(id,t) when makeLooseNeedSafe t -> [Pkg.Derived.safe id]
  | D_safe(id,t) when not (makeLooseNeedSafe t) -> [Pkg.Derived.loose id]
  | D_value _ ->
    let id = d.d_ident in
    [
      Pkg.Derived.signal id;
      Pkg.Derived.getter id
    ]
  | D_state _ ->
    let id = d.d_ident in
    [
      Pkg.Derived.signal id;
      Pkg.Derived.getter id;
      Pkg.Derived.setter id
    ]
  | D_array _ ->
    let id = d.d_ident in
    let data = Pkg.Derived.data id in
    [
      data ;
      Pkg.Derived.loose data ;
      Pkg.Derived.safe data ;
      Pkg.Derived.order data ;
      Pkg.Derived.signal id ;
      Pkg.Derived.reload id ;
      Pkg.Derived.fetch id ;
    ]
  | _ -> []

let next m id =
  let r = m.rank in
  m.mark <- Pkg.IdMap.add id r m.mark ;
  m.rank <- succ r

let rec mark m d =
  let id = d.Pkg.d_ident in
  if not (Pkg.IdMap.mem id m.mark) then
    ( List.iter (mark_id m) (depends d) ; next m id )

and mark_id m id =
  try mark m (Pkg.IdMap.find id m.index)
  with Not_found -> ()

let ranking ds =
  let index = List.fold_left
      (fun m d -> Pkg.IdMap.add d.Pkg.d_ident d m)
      Pkg.IdMap.empty ds in
  let m = { rank = 0 ; mark = Pkg.IdMap.empty ; index } in
  List.iter (mark m) ds ;
  let rk = m.mark in
  let getRank a = try Pkg.IdMap.find a.Pkg.d_ident rk with Not_found -> 0 in
  List.sort (fun a b -> getRank a - getRank b) ds

(* -------------------------------------------------------------------------- *)
(* --- Package Generator                                                  --- *)
(* -------------------------------------------------------------------------- *)

let pkg_path ~plugin ~package =
  String.concat "/" @@
  let pkg = "api" :: package in
  "frama-c" ::
  match plugin with
  | Pkg.Kernel -> "kernel" :: pkg
  | Pkg.Plugin p -> "plugins" :: p :: pkg

let makeIgnore fmt msg =
  Format.fprintf fmt "//@ts-ignore@\n" ;
  Format.fprintf fmt msg

(* path shall be [pkg_path] of [pkg] *)
let makePackage pkg path fmt =
  begin
    let open Pkg in
    Format.fprintf fmt "/* --- Generated Frama-C Server API --- */@\n@\n" ;
    Format.fprintf fmt "/**@\n   %s@\n" pkg.p_title ;
    if pkg.p_descr <> [] then
      Format.fprintf fmt "@\n   @[<hov 0>%a@]@\n@\n" pp_descr pkg.p_descr ;
    Format.fprintf fmt "   @@packageDocumentation@\n" ;
    Format.fprintf fmt "   @@module %s@\n" path ;
    Format.fprintf fmt "*/@\n@." ;
    let names = Pkg.resolve ~keywords pkg in
    makeIgnore fmt "import * as Json from 'dome/data/json';@\n" ;
    makeIgnore fmt "import * as Compare from 'dome/data/compare';@\n" ;
    makeIgnore fmt "import * as Server from 'frama-c/server';@\n" ;
    makeIgnore fmt "import * as State from 'frama-c/states';@\n" ;
    Format.pp_print_newline fmt () ;
    Pkg.IdMap.iter
      (fun { name = iname ; plugin ; package } name ->
         if plugin <> pkg.p_plugin || package <> pkg.p_package
         then
           let path = pkg_path ~plugin ~package in
           if iname = name then
             makeIgnore fmt "import { %s } from '%s';@\n"
               name path
           else
             makeIgnore fmt "import { %s: %s } from '%s';@\n"
               iname name path
      ) names ;
    List.iter
      (makeDeclaration fmt names)
      (ranking pkg.p_content) ;
    Format.pp_print_newline fmt () ;
    Format.fprintf fmt "/* ------------------------------------- */@." ;
  end

(* -------------------------------------------------------------------------- *)
(* --- Main Generator                                                     --- *)
(* -------------------------------------------------------------------------- *)

let generate () =
  begin
    Pkg.iter
      begin fun pkg ->
        let path = pkg_path ~plugin:pkg.p_plugin ~package:pkg.p_package in
        Self.feedback "Package %s" path ;
        let out = OUT.get () in
        let file = Printf.sprintf "%s/%s/index.ts" out path in
        let dir = Filename.dirname file in
        if not (Sys.file_exists dir && Sys.is_directory dir) then
          Extlib.mkdir ~parents:true dir 0o755 ;
        Command.print_file file (makePackage pkg path) ;
      end
  end

let () = Db.Main.extend generate

(* -------------------------------------------------------------------------- *)
