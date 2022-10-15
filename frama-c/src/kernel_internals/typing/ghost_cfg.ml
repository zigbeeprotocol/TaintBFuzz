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

open Cil
open Cil_types
open Visitor_behavior

module Stmt = Cil_datatype.Stmt
module StmtSet = Stmt.Hptset

let error = Kernel.warning ~wkey:Kernel.wkey_ghost_bad_use


let annot_attr = "has_annot"

(* During the creation of the no ghost AST, when a stmt has some annotation,
   we add an attribute to its copy.
*)
let has_annot stmt =
  Annotations.code_annot stmt <> [] ||
  Cil.hasAttribute annot_attr stmt.sattr

let noGhostFD prj fd =
  let visitor = object (self)
    inherit genericCilVisitor (refresh prj)

    method private original = Get_orig.stmt self#behavior

    method! vstmt s =
      if s.ghost then begin
        s.skind <- Instr(Skip (Stmt.loc s)) ;
        s.labels <- [] ;
        s.ghost <- false ;
        SkipChildren
      end else
        begin match s.skind with
          | Switch(e, block, cases, loc) ->
            let cases = List.filter
                (fun s -> not (self#original s).ghost) cases
            in
            s.skind <- Switch(e, block, cases, loc) ;
            DoChildren
          | _ ->
            let o = self#original s in
            s.sattr <- if has_annot o then [AttrAnnot annot_attr] else [] ;
            DoChildren
        end

    method! vblock b =
      if Cil.is_ghost_else b then begin
        b.bstmts <- [] ;
        b.battrs <- Cil.dropAttribute Cil.frama_c_ghost_else b.battrs ;
        SkipChildren
      end else
        DoChildren

    method getBehavior () = self#behavior
  end in
  (visitCilFunction (visitor :> cilVisitor) fd), (visitor#getBehavior ())

type follower =
  (* For a stmt, an "Infinite" follower means that following skip instructions
     we just go back to this stmt. *)
  | Infinite | Exit | Stmt of stmt

let sync stmt =
  match stmt.skind with
  (* We do not synchronize on a block: its successor is the first statement that
     it contains. Thus, we will synchronize later, on the first interesting stmt
     we can reach when we enter the block.
  *)
  (* Note that a stmt with an annotation is always interesting. *)
  | Instr(Skip(_)) | Block(_) | Continue(_) | Break(_) -> has_annot stmt
  | _ -> true

let nextSync stmt =
  let rec aux visited s =
    if StmtSet.mem s visited then Infinite
    else match sync s with
      | true -> Stmt s
      | false when s.succs = [] -> Exit
      | _ ->
        aux (StmtSet.add s visited) (Extlib.as_singleton s.succs)
  in aux StmtSet.empty stmt

let nextNonGhostSync stmt =
  let rec do_find (res, visited) stmt =
    if StmtSet.mem stmt visited then res, visited
    else begin
      let visited = StmtSet.add stmt visited in
      if not (sync stmt) then
        do_find (res, visited) (Extlib.as_singleton stmt.succs)
      else if not (stmt.ghost) then StmtSet.add stmt res, visited
      else List.fold_left do_find (res, visited) stmt.succs
    end
  in
  fst (do_find (StmtSet.empty, StmtSet.empty) stmt)

let alteredCFG stmt =
  error ~once:true ~source:(fst (Stmt.loc stmt))
    "Ghost code breaks CFG starting at:@.%a"
    Cil_printer.pp_stmt stmt

let checkGhostCFG bhv withGhostStart noGhost =
  let rec do_check visited withGhostStart noGhostStart =
    match (nextSync withGhostStart), (nextSync noGhostStart) with
    | Stmt withGhost, Stmt noGhost ->
      let is_visited = StmtSet.mem withGhost visited in
      let visited = StmtSet.add withGhost visited in
      let withGhost =
        StmtSet.contains_single_elt (nextNonGhostSync withGhost)
      in
      begin match withGhost, noGhost with
        | Some s1, s2 when not (Stmt.equal s1 (Get_orig.stmt bhv s2)) ->
          alteredCFG withGhostStart ; visited

        (* Note: this test is deferred so that bad stmts are detected above *)
        | Some _, _ when is_visited -> visited

        | Some ({ skind = If(_) } as withGhost), noGhost ->
          let wgThen, wgElse = Cil.separate_if_succs withGhost in
          let ngThen, ngElse = Cil.separate_if_succs noGhost in
          let visited = do_check visited wgThen ngThen in
          do_check visited wgElse ngElse

        | Some ({ skind = Switch(_) } as withGhost), noGhost ->
          let ngSuccs, ngDef = Cil.separate_switch_succs noGhost in
          let wgAllSuccs, wgDef = Cil.separate_switch_succs withGhost in
          let wgSuccsG, wgSuccsNG =
            List.partition (fun s -> s.ghost) wgAllSuccs
          in
          let mustDefault = wgDef :: wgSuccsG in
          assert(List.length ngSuccs = List.length wgSuccsNG) ;
          let visited = List.fold_left2 do_check visited wgSuccsNG ngSuccs in
          List.fold_left (fun v s -> do_check v s ngDef) visited mustDefault

        | Some ({ skind=Loop(_,wgb,_,_,_) }), { skind=Loop (_,ngb,_,_,_) } ->
          begin match wgb.bstmts, ngb.bstmts with
            | s1 :: _ , s2 :: _ -> do_check visited s1 s2
            | _, _ -> visited
          end

        | Some { succs = [wg] }, { succs = [ng] } -> do_check visited wg ng
        | Some { succs = [] }, { succs = [] } -> visited
        | _, _  -> alteredCFG withGhostStart ; visited
      end
    | Exit, Exit | Infinite, Infinite -> visited
    | _ , _ -> alteredCFG withGhostStart ; visited
  in
  ignore (do_check StmtSet.empty withGhostStart noGhost)

let checkGhostCFGInFun prj fd =
  if fd.svar.vghost then ()
  else begin
    let noGhostFD, bhv = noGhostFD prj fd in
    Cfg.clearCFGinfo ~clear_id:false noGhostFD ;
    Cfg.cfgFun noGhostFD ;
    checkGhostCFG bhv (List.hd fd.sbody.bstmts) (List.hd noGhostFD.sbody.bstmts)
  end

let checkGhostCFGInFile (f : file) =
  let project = Project.create "NO_GHOST" in
  Cil.iterGlobals f (function
      | GFun (fd, _) -> checkGhostCFGInFun project fd
      | _ -> ()) ;
  Project.remove ~project ()

let transform_category =
  File.register_code_transformation_category "Ghost CFG checking"

let () =
  File.add_code_transformation_after_cleanup
    transform_category checkGhostCFGInFile
