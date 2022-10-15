(**************************************************************************)
(*                                                                        *)
(*  This file is part of WP plug-in of Frama-C.                           *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat a l'energie atomique et aux energies              *)
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

(* -------------------------------------------------------------------------- *)
(* --- Compute Reachability for Smoke Tests                               --- *)
(* -------------------------------------------------------------------------- *)

type flow =
  | F_goto    (* single successor for node *)
  | F_effect  (* single successor with must-be-reach effect *)
  | F_call    (* multiple successors with must-be-reach effect *)
  | F_branch  (* branching node *)
  | F_return  (* return node *)
  | F_entry   (* function or loop entry node *)
  | F_dead    (* truly dead code *)

type node = {
  id : int ;
  mutable flow : flow ;
  mutable prev : node list ;
  mutable protected : bool option ;
  (* whether the node is dominated by unreachable node or by a smoke test *)
  mutable unreachable : bool option ;
  (* whether the node is unreachable from the entry point *)
}

let kid = ref 0

let node () =
  incr kid ;
  { id = !kid ; prev = [] ;
    protected = None ;
    unreachable = None ;
    flow = F_goto }

(* -------------------------------------------------------------------------- *)
(* --- Unrolled Loop                                                      --- *)
(* -------------------------------------------------------------------------- *)

let is_unrolled_completely spec =
  match spec.term_node with
  | TConst (LStr "completely") -> true
  | _ -> false

let rec is_predicate cond p =
  match p.pred_content with
  | Pfalse -> not cond
  | Ptrue -> cond
  | Pnot p -> is_predicate (not cond) p
  | Pforall(_,p) | Pexists(_,p) | Plet(_,p) -> is_predicate cond p
  | Pif(_,p,q) -> is_predicate cond p && is_predicate cond q
  | Pat(p,_) -> is_predicate cond p
  | Pand(p,q) ->
    if cond
    then is_predicate true p && is_predicate true q
    else is_predicate false p || is_predicate false q
  | Por(p,q) ->
    if cond
    then is_predicate true p && is_predicate true q
    else is_predicate false p && is_predicate false q
  | Pimplies(p,q) ->
    if cond
    then is_predicate false p || is_predicate true q
    else is_predicate true p && is_predicate false q
  | _ -> false

let is_dead_annot ca =
  match ca.annot_content with
  | APragma (Loop_pragma (Unroll_specs [ spec ; _ ])) ->
    is_unrolled_completely spec
  | AAssert([],p)
  | AInvariant([],_,p) ->
    Logic_utils.use_predicate p.tp_kind && is_predicate false p.tp_statement
  | _ -> false

let is_dead_code stmt =
  let exception Deadcode in
  try
    Annotations.iter_code_annot (fun _emitter ca ->
        if is_dead_annot ca then raise Deadcode
      ) stmt ;
    false
  with Deadcode -> true

(* -------------------------------------------------------------------------- *)
(* --- Compute CFG                                                        --- *)
(* -------------------------------------------------------------------------- *)

type reachability = node Stmt.Map.t
type cfg = reachability ref (* working cfg during compilation *)

let of_stmt cfg s =
  try Stmt.Map.find s !cfg with Not_found ->
    let n = node () in
    cfg := Stmt.Map.add s n !cfg ; n

let goto a b =
  b.prev <- a :: b.prev ;
  if b.flow = F_dead then F_dead else F_goto

let flow i f =
  if f = F_dead then F_dead else
    match i with
    | Asm _ | Set _ -> F_effect
    | Local_init _ ->
      if Wp_parameters.SmokeDeadlocalinit.get ()
      then F_effect
      else F_goto
    | Call _ -> F_call
    | Skip _ | Code_annot _ -> F_goto

let merge a b = match a,b with
  | F_dead , F_dead -> F_dead
  | _ -> F_branch

type env = {
  cfg: cfg ;
  break: node ;
  continue: node ;
}

let rec stmt env s b =
  let a = of_stmt env.cfg s in
  let f = skind env a b s.skind in
  a.flow <- if is_dead_code s then F_dead else f ; a

and skind env a b = function
  | Instr i -> flow i (goto a b)
  | Return (None,_) -> F_goto
  | Return (Some _,_) -> F_return
  | Goto (lbl,_) -> goto a (of_stmt env.cfg !lbl)
  | Break _ -> goto a env.break
  | Continue _ -> goto a env.continue
  | If(_,bthen,belse,_) ->
    let ft = goto a (block env bthen b) in
    let fe = goto a (block env belse b) in
    merge ft fe
  | Switch(_,body,cases,_) ->
    ignore (block { env with break = b } body b) ;
    List.fold_left
      (fun f s -> merge f (goto a (of_stmt env.cfg s)))
      F_dead cases
  | Loop(_,body,_,_,_) ->
    let continue = node () in
    let lenv = { env with continue ; break = b }  in
    let flow = goto a (block lenv body continue) in
    if flow = F_dead then F_dead else F_entry
  | Block body ->
    goto a (block env body b)
  | UnspecifiedSequence s ->
    let body = Cil.block_from_unspecified_sequence s in
    goto a (block env body b)
  | Throw _ | TryCatch _ | TryFinally _ | TryExcept _ ->
    Wp_parameters.not_yet_implemented "try-catch blocks"

and block env blk b = sequence env blk.bstmts b
and sequence env seq b = match seq with
  | [] -> b
  | s :: seq -> stmt env s (sequence env seq b)

(* -------------------------------------------------------------------------- *)
(* --- Compute Reachability                                               --- *)
(* -------------------------------------------------------------------------- *)

let rec unreachable node =
  match node.unreachable with
  | Some r -> r
  | None ->
    node.unreachable <- Some true ; (* cut loops *)
    let r =
      match node.flow with
      | F_dead -> true
      | F_entry -> false
      | F_goto | F_effect | F_return | F_branch | F_call ->
        List.for_all unreachable node.prev
    in node.unreachable <- Some r ; r

let rec protected node =
  match node.protected with
  | Some r -> r
  | None ->
    node.protected <- Some false ; (* cut loops *)
    let r =
      match node.flow with
      | F_dead | F_entry -> true
      | F_goto | F_effect | F_return | F_branch | F_call ->
        node.prev <> [] && List.for_all protected_by node.prev
    in node.protected <- Some r ; r

and protected_by prev =
  match prev.flow with
  | F_dead | F_entry | F_effect -> true
  | F_goto -> protected prev
  | F_call | F_branch | F_return -> unreachable prev

let smoking_node n =
  match n.flow with
  | F_effect | F_call | F_return -> not (protected n)
  | F_goto | F_branch | F_entry | F_dead -> false

(* returns true if the stmt requires a reachability smoke test *)
let smoking reachability stmt =
  try Stmt.Map.find stmt reachability |> smoking_node
  with Not_found -> true

let compute kf =
  try
    let f = Kernel_function.get_definition kf in
    let cfg = ref Stmt.Map.empty in
    let returned = node () in
    let continue = node () in
    let break = node () in
    let entry = node () in
    let body = block { cfg ; break ; continue } f.sbody returned in
    let _ = goto entry body in
    entry.flow <- F_entry ; !cfg
  with Kernel_function.No_Definition ->
    Stmt.Map.empty

(* ---------------------------------------------------------------------- *)
(* --- Dump for debugging                                             --- *)
(* ---------------------------------------------------------------------- *)

module G = Dotgraph
module Nmap = Map.Make(struct type t = node let compare a b = a.id - b.id end)
module N = Dotgraph.Node(Nmap)

let dump ~dir kf reached =
  let name = Kernel_function.get_name kf in
  let file = Format.asprintf "%a/%s.dot" Datatype.Filepath.pretty dir name in
  let dot = G.open_dot ~file ~name () in
  N.define dot
    (fun a na ->
       let attr =
         if smoking_node a then [`Filled;`Fillcolor "orange"]
         else if protected a then [`Filled;`Fillcolor "green"]
         else if unreachable a then [`Filled;`Fillcolor "red"]
         else []
       in G.node dot na attr ;
       List.iter
         (fun b ->
            let attr = match b.flow with
              | F_call | F_branch | F_return | F_dead -> [`Dotted;`ArrowForward]
              | F_effect | F_entry | F_goto -> [`ArrowForward]
            in G.edge dot (N.get b) na attr)
         a.prev
    ) ;
  Stmt.Map.iter
    (fun s n ->
       let label =
         let module Pu = Pretty_utils in
         let module Pr = Printer in
         match s.skind with
         | Instr _ | Return _ | Break _ | Continue _ | Goto _ ->
           Pu.to_string Pr.pp_stmt s
         | If(e,_,_,_) -> Format.asprintf "@[<hov 2>if (%a)@]" Pr.pp_exp e
         | Switch(e,_,_,_) -> Format.asprintf "@[<hov 2>switch (%a)@]" Pr.pp_exp e
         | Loop _ -> Printf.sprintf "Loop s%d" s.sid
         | Block  _ -> Printf.sprintf "Block s%d" s.sid
         | UnspecifiedSequence  _ -> Printf.sprintf "Seq. s%d" s.sid
         | Throw _ | TryExcept _ | TryCatch _ | TryFinally _ ->
           Printf.sprintf "Exn. s%d" s.sid
       in G.node dot (N.get n)
         [`Box;`Label (Printf.sprintf "s%d n%d: %s" s.sid n.id label)])
    reached ;
  G.run dot ;
  G.close dot ;
  let out = G.layout dot in
  Wp_parameters.result "Reached Graph: %s" out

(* ---------------------------------------------------------------------- *)
(* --- Projectified Analysis Result                                   --- *)
(* ---------------------------------------------------------------------- *)

module FRmap = Kernel_function.Make_Table
    (Datatype.Make
       (struct
         type t = reachability
         include Datatype.Serializable_undefined
         let reprs = [Stmt.Map.empty]
         let name = "WpReachable.reached"
       end))
    (struct
      let name = "WpReachable.compute"
      let dependencies = [Ast.self]
      let size = 17
    end)

let dkey = Wp_parameters.register_category "reached"

let reachability = FRmap.memo
    begin fun kf ->
      let r = compute kf in
      (if Wp_parameters.has_dkey dkey then
         let dir = Wp_parameters.get_session_dir ~force:true "reach" in
         dump ~dir kf r ) ; r
    end

(* -------------------------------------------------------------------------- *)
(* --- Doome Status                                                       --- *)
(* -------------------------------------------------------------------------- *)

module Invalid_behaviors = struct
  module String_set = Datatype.String.Set

  include State_builder.Hashtbl(Kernel_function.Hashtbl)(String_set)
      (struct
        let name = "Wp.WpReached.Invalid_behavior"
        let dependencies = [Ast.self]
        let size = 32
      end)

  let add kf bhv =
    let set =
      try find kf
      with Not_found -> String_set.empty
    in
    add kf (String_set.add bhv.b_name set)

  let mem kf bhv =
    try String_set.mem bhv.b_name (find kf)
    with Not_found -> false
end

let set_invalid emitter tgt =
  let open Property_status in
  match tgt with
  (* For invalid assumes, introduce "ensures false" in behavior on need *)
  | Property.IPPredicate { ip_kind = PKAssumes(bhv) ; ip_kf ; ip_pred } ->
    if not (Invalid_behaviors.mem ip_kf bhv) then begin
      Invalid_behaviors.add ip_kf bhv ;
      let pred_name = [ "Wp" ; "SmokeTest" ] in
      let pred_loc = ip_pred.ip_content.tp_statement.pred_loc in
      let p = { Logic_const.pfalse with pred_loc ; pred_name } in
      let p = Logic_const.(new_predicate p) in
      let pid = Property.ip_of_ensures ip_kf Kglobal bhv (Normal, p) in
      Annotations.add_ensures emitter ip_kf ~behavior:bhv.b_name [Normal, p];
      emit emitter ~hyps:[] pid False_if_reachable
    end
  | p ->
    emit emitter ~hyps:[] p False_if_reachable

let set_doomed emitter pid =
  List.iter (set_invalid emitter) (WpPropId.doomed_if_valid pid) ;
  match WpPropId.unreachable_if_valid pid with
  | Property.OLStmt(kf,stmt) ->
    let ca =
      match Annotations.code_annot ~emitter ~filter:is_dead_annot stmt with
      | ca::_ -> ca
      | [] ->
        let pred_loc = Stmt.loc stmt in
        let pred_name = [ "Wp" ; "SmokeTest" ] in
        let pf = { Logic_const.pfalse with pred_loc ; pred_name } in
        let pf = Logic_const.toplevel_predicate pf in
        let ca = Logic_const.new_code_annotation (AAssert ([],pf)) in
        Annotations.add_code_annot emitter ~kf stmt ca ; ca
    in
    List.iter (set_invalid emitter) (Property.ip_of_code_annot kf stmt ca)
  | Property.OLGlob _ | Property.OLContract _ -> ()

(* -------------------------------------------------------------------------- *)
(* --- Status of Unreachable Annotations                                  --- *)
(* -------------------------------------------------------------------------- *)

let dkey = Wp_parameters.register_category "reach" (* debugging key *)
let debug fmt = Wp_parameters.debug ~dkey fmt

let unreachable_proved = ref 0
let unreachable_failed = ref 0

let wp_unreachable =
  Emitter.create
    "Unreachable Annotations"
    [ Emitter.Property_status ]
    ~correctness:[] (* TBC *)
    ~tuning:[] (* TBC *)

let set_unreachable pid =
  if WpPropId.is_smoke_test pid then
    begin
      let source = WpPropId.source_of_id pid in
      set_doomed wp_unreachable pid ;
      incr unreachable_failed ;
      Wp_parameters.warning ~source "Failed smoke-test"
    end
  else
    let open Property in
    let emit = function
      | IPPredicate {ip_kind = PKAssumes _} -> ()
      | p ->
        debug "unreachable annotation %a@." Property.pretty p;
        Property_status.emit wp_unreachable ~hyps:[] p Property_status.True
    in
    let pids = match WpPropId.property_of_id pid with
      | IPPredicate {ip_kind = PKAssumes _} -> []
      | IPBehavior {ib_kf; ib_kinstr; ib_active; ib_bhv} ->
        let active = Datatype.String.Set.elements ib_active in
        (ip_post_cond_of_behavior ib_kf ib_kinstr ~active ib_bhv) @
        (ip_requires_of_behavior ib_kf ib_kinstr ib_bhv)
      | IPExtended _ -> []
      (* Extended clauses might concern anything. Don't validate them
         unless we know exactly what is going on. *)
      | p ->
        incr unreachable_proved ;
        Wp_parameters.result "[CFG] Goal %a : Valid (Unreachable)"
          WpPropId.pp_propid pid ; [p]
    in
    List.iter emit pids

(* -------------------------------------------------------------------------- *)
