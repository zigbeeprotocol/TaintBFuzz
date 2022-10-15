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

open Cil_types
open Cil_datatype

module Options = Reduc_options

exception Alarm_reached

let dkey = Options.register_category "collect"
let debug = Options.debug ~dkey

type 'a alarm_component = Emitter.t ->
  kernel_function ->
  stmt ->
  rank:int -> Alarms.alarm -> code_annotation -> 'a -> 'a

type annoth = AnnotAll | AnnotInout

type env = {
  rel_annoth: annoth;
  rel_stmts: Stmt.Set.t;
  rel_vars: LvalStructEq.Set.t Stmt.Map.t;
}

let empty_env annoth = {
  rel_annoth = annoth;
  rel_stmts = Stmt.Set.empty;
  rel_vars = Stmt.Map.empty;
}

let env_with_stmt env stmt =
  { env with rel_stmts = Stmt.Set.add stmt env.rel_stmts }

let env_with_stmt_vars env stmt lvs =
  let vars =
    try
      Stmt.Map.find stmt env.rel_vars
    with Not_found -> LvalStructEq.Set.empty in
  let new_vars = LvalStructEq.Set.(union vars (of_list lvs)) in
  { env with rel_vars = Stmt.Map.add stmt new_vars env.rel_vars }

(* ************************************************************************ *)
(** Alarms to relevant locations *)
(* ************************************************************************ *)

class stmts_vis
    (alarm_stmt : stmt)
    (env: env ref) = object(_)
  inherit Cil.nopCilVisitor

  method! vstmt stmt =
    env := env_with_stmt !env stmt;
    if Stmt.equal stmt alarm_stmt then begin
      raise Alarm_reached
    end;
    Cil.DoChildren
end

let rec collect_off typ =
  match typ with
  | TInt _ | TFloat _ -> [ NoOffset ]
  | TComp ({cfields = Some flds}, _) ->
    List.fold_left collect_fields [] flds
  | TArray (arrtyp, e_opt, _) ->
    debug "Array of length %a" (Pretty_utils.pp_opt Printer.pp_exp) e_opt;
    begin try collect_array arrtyp [] (Cil.lenOfArray64 e_opt)
      with Cil.LenOfArray _ -> [] end
  | TVoid _ | TFun _ | TPtr _ | TEnum _ | TNamed _ | TBuiltin_va_list _
  | TComp ({cfields = None}, _)-> []

and collect_fields acc fld =
  let offs = collect_off fld.ftype in
  List.map (fun off -> Field (fld, off)) offs @ acc

and collect_array typ acc = function
  | x when Integer.is_zero x -> acc
  | x ->
    let offs = collect_off typ in
    let exp = Cil.kinteger64 ~loc:Location.unknown x in
    let acc' = acc @ List.map (fun off -> Index(exp ,off)) offs in
    collect_array typ acc' (Integer.add x Integer.minus_one)

let collect_varinfo acc x =
  let offs = collect_off x.vtype in
  List.map (fun off -> (Var x, off)) offs @ acc

class inout_vis
    (alarm_stmt : stmt)
    (kf : Kernel_function.t)
    (env : env ref) = object(self)
  inherit stmts_vis alarm_stmt env as super

  val mutable vars = []

  method !vfunc _ =
    vars <- Kernel_function.((get_locals kf) @ (get_formals kf));
    Cil.DoChildren

  method private is_first_stmt stmt =
    try Stmt.equal stmt (Kernel_function.find_first_stmt kf)
    with Kernel_function.No_Statement -> assert false

  method !vstmt stmt =
    let out = !Db.Outputs.statement stmt in
    let filter_out vi =
      let open Locations in
      let zone = enumerate_bits (loc_of_varinfo vi) in
      Zone.intersects out zone
    in
    let effect =
      if self#is_first_stmt stmt then vars
      else List.filter filter_out vars
    in
    let vars = List.fold_left collect_varinfo [] effect in
    env := env_with_stmt_vars !env stmt vars;
    super#vstmt stmt
end

let get_relevant_stmts kf stmt env =
  let do_visit ref_env = match !ref_env.rel_annoth with
    | AnnotAll -> Cil.visitCilFunction (new stmts_vis stmt ref_env)
    | AnnotInout ->
      Cil.visitCilFunction (new inout_vis stmt kf ref_env :> Cil.cilVisitor)
  in
  let renv = ref env in
  try
    let fundec = Kernel_function.get_definition kf in
    ignore (do_visit renv fundec);
    !renv
  with Alarm_reached ->
    !renv

let get_relevant _emit kf stmt ~rank:_ _a _annot env =
  get_relevant_stmts kf stmt env

let should_annotate_stmt env stmt =
  Stmt.Set.mem stmt env.rel_stmts

(* ************************************************************************ *)
(** Relevant locations to relevant variables *)
(* ************************************************************************ *)

class relevant_stmt_vars_visitor
    (vars: LvalStructEq.Set.t ref) = object(_)
  inherit Cil.nopCilVisitor

  method! vstmt stmt =
    match stmt.skind with
    | Goto _ | UnspecifiedSequence _ -> Cil.SkipChildren
    | _ -> Cil.DoChildren

  method! vblock _ = Cil.SkipChildren

  method !vexpr e =
    begin match e.enode with
      | Lval lv | AddrOf lv | StartOf lv ->
        vars := LvalStructEq.Set.add lv !vars
      | _ -> ()
    end;
    Cil.DoChildren
end

let get_relevant_all_vars_stmt kf stmt =
  let do_visit ref_vars =
    Cil.visitCilStmt (new relevant_stmt_vars_visitor ref_vars)
  in
  let ref_vars = ref LvalStructEq.Set.empty in
  ignore (do_visit ref_vars stmt);
  let locals = Kernel_function.get_locals kf in
  let formals = Kernel_function.get_formals kf in
  let vars = List.map Cil.var (locals @ formals) in
  vars @ LvalStructEq.Set.elements !ref_vars

let get_relevant_inout_vars_stmt env stmt =
  try
    let vars = Stmt.Map.find stmt env.rel_vars in
    LvalStructEq.Set.elements vars
  with Not_found -> assert false

let get_relevant_vars_stmt env kf stmt = match env.rel_annoth with
  | AnnotAll -> get_relevant_all_vars_stmt kf stmt
  | AnnotInout -> get_relevant_inout_vars_stmt env stmt
