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

open Server
open Cil_types

let package =
  Package.package ~plugin:"studia" ~name:"studia" ~title:"Studia"
    ~readme:"studia.md" ()

type effects =
  { direct: stmt list;
    indirect: stmt list; }

module Effects = struct
  open Server.Data

  type record
  let record: record Record.signature = Record.signature ()

  module Location = Data.Jpair (Kernel_ast.Kf) (Kernel_ast.Marker)

  let direct = Record.field record ~name:"direct"
      ~descr:(Markdown.plain "List of statements with direct effect.")
      (module Data.Jlist (Location))
  let indirect = Record.field record ~name:"indirect"
      ~descr:(Markdown.plain "List of statements with indirect effect.")
      (module Data.Jlist (Location))

  let data = Record.publish record ~package ~name:"effects"
      ~descr:(Markdown.plain "Statements that read or write a location.")

  module R : Record.S with type r = record = (val data)
  type t = effects
  let jtype = R.jtype

  let to_json effects =
    let output_stmt stmt =
      let kf = Kernel_function.find_englobing_kf stmt in
      kf, Printer_tag.PStmtStart (kf, stmt)
    in
    R.default |>
    R.set direct (List.map output_stmt effects.direct) |>
    R.set indirect (List.map output_stmt effects.indirect) |>
    R.to_json
end


type kind = Reads | Writes

let compute kind zone =
  let stmts = match kind with
    | Reads -> Reads.compute zone
    | Writes -> Writes.compute zone
  in
  let add_if b stmt acc = if b then stmt :: acc else acc in
  let add acc (stmt, e) =
    let direct = add_if e.Writes.direct stmt acc.direct in
    let indirect = add_if e.Writes.indirect stmt acc.indirect in
    { direct; indirect }
  in
  let empty = { direct = []; indirect = []; } in
  List.fold_left add empty stmts

let lval_location kinstr lval =
  Eva.Results.(before_kinstr kinstr |> eval_address lval |> as_zone)

let () = Request.register ~package
    ~kind:`GET ~name:"getReadsLval"
    ~descr:(Markdown.plain "Get the list of statements that read a lval.")
    ~input:(module Kernel_ast.Lval)
    ~output:(module Effects)
    (fun (kinstr, lval) -> compute Reads (lval_location kinstr lval))

let () = Request.register ~package
    ~kind:`GET ~name:"getWritesLval"
    ~descr:(Markdown.plain "Get the list of statements that write a lval.")
    ~input:(module Kernel_ast.Lval)
    ~output:(module Effects)
    (fun (kinstr, lval) -> compute Writes (lval_location kinstr lval))
