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

let package = Pkg.package ~name:"project"
    ~title:"Project Management" ~readme:"project.md" ()

(* -------------------------------------------------------------------------- *)
(* --- Project Info                                                       --- *)
(* -------------------------------------------------------------------------- *)

module ProjectId = (val jkey ~kind:"project")

module ProjectInfo =
struct
  type t = Project.t
  let jtype = Data.declare ~package
      ~name:"projectInfo"
      ~descr:(Md.plain "Project informations")
      Pkg.(Jrecord [
          "id",ProjectId.jtype;
          "name",Jalpha;
          "current",Jboolean;
        ])

  let of_json js =
    Js.member "id" js |> Js.to_string |> Project.from_unique_name

  let to_json p =
    `Assoc [
      "id", `String (Project.get_unique_name p) ;
      "name", `String (Project.get_name p) ;
      "current", `Bool (Project.is_current p) ;
    ]
end

(* -------------------------------------------------------------------------- *)
(* --- Project Requests                                                   --- *)
(* -------------------------------------------------------------------------- *)

module ProjectRequest =
struct

  (* forward request on a given project *)

  type t = Project.t * string * json

  let jtype = Data.declare ~package ~name:"projectRequest"
      ~descr:(Md.plain "Request to be executed on the specified project.")
      (Jrecord [
          "project",ProjectId.jtype;
          "request",Jstring;
          "data",Jany;
        ])

  let of_json js =
    begin
      Project.from_unique_name Js.(member "project" js |> to_string) ,
      Js.(member "request" js |> to_string) ,
      Js.(member "data" js)
    end

  let process kind (project,request,data) =
    match Main.find request with
    | Some(kd,handler) when kd = kind -> Project.on project handler data
    | Some _ -> failwith (Printf.sprintf "Incompatible kind for '%s'" request)
    | None -> failwith (Printf.sprintf "Request '%s' undefined" request)

end

(* -------------------------------------------------------------------------- *)
(* --- Project Requests                                                   --- *)
(* -------------------------------------------------------------------------- *)

let () = Request.register ~package
    ~kind:`GET ~name:"getCurrent"
    ~descr:(Md.plain "Returns the current project")
    ~input:(module Junit) ~output:(module ProjectInfo)
    Project.current

let () = Request.register ~package
    ~kind:`SET ~name:"setCurrent"
    ~descr:(Md.plain "Switches the current project")
    ~input:(module ProjectId) ~output:(module Junit)
    (fun pid -> Project.(set_current (from_unique_name pid)))

let () = Request.register ~package
    ~kind:`GET ~name:"getList"
    ~descr:(Md.plain "Returns the list of all projects")
    ~input:(module Junit) ~output:(module Jlist(ProjectInfo))
    (fun () -> Project.fold_on_projects (fun ids p -> p :: ids) [])

let () = Request.register ~package
    ~kind:`GET ~name:"getOn"
    ~descr:(Md.plain "Execute a GET request within the given project")
    ~input:(module ProjectRequest) ~output:(module Jany)
    (ProjectRequest.process `GET)

let () = Request.register ~package
    ~kind:`SET ~name:"setOn"
    ~descr:(Md.plain "Execute a SET request within the given project")
    ~input:(module ProjectRequest) ~output:(module Jany)
    (ProjectRequest.process `SET)

let () = Request.register ~package
    ~kind:`EXEC ~name:"execOn"
    ~descr:(Md.plain "Execute an EXEC request within the given project")
    ~input:(module ProjectRequest) ~output:(module Jany)
    (ProjectRequest.process `EXEC)

(* -------------------------------------------------------------------------- *)
(* --- Project Management                                                 --- *)
(* -------------------------------------------------------------------------- *)

let () =
  Request.register
    ~package
    ~descr:(Md.plain "Create a new project")
    ~kind:`SET
    ~name:"create"
    ~input:(module Jstring)
    ~output:(module ProjectInfo)
    Project.create

(* -------------------------------------------------------------------------- *)
