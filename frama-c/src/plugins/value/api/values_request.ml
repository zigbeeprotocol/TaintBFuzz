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
open Data
open Cil_types

module Kmap = Kernel_function.Hashtbl
module Smap = Cil_datatype.Stmt.Hashtbl
module CS = Value_types.Callstack
module CSet = CS.Set
module CSmap = CS.Hashtbl

module Md = Markdown
module Jkf = Kernel_ast.Kf
module Jstmt = Kernel_ast.Stmt
module Jmarker = Kernel_ast.Marker

let package =
  Package.package
    ~plugin:"eva"
    ~name:"values"
    ~title:"Eva Values"
    ~readme:"eva.md"
    ()

type probe =
  | Pexpr of exp * stmt
  | Plval of lval * stmt

type callstack = Value_types.callstack
type truth = Abstract_interp.truth

(* The result of an evaluation:
   - the resulting value as a text to be printed;
   - the alarms emitted for the evaluation;
   - the variables pointed by the resulting value, if any. *)
type evaluation = {
  value: string;
  alarms: ( truth * string ) list ;
  pointed_vars: (string * Printer_tag.localizable) list;
}

(* Evaluations after the given statement. If the statement is a conditional
   branch, evaluations in the [then] and [else] branch. *)
type 'v next =
  | After of 'v
  | Cond of 'v * 'v
  | Nothing

type evaluations = {
  here: evaluation;
  next: evaluation next;
}

let signal = Request.signal ~package ~name:"changed"
    ~descr:(Md.plain "Emitted when EVA results has changed")

let () = Analysis.register_computation_hook ~on:Computed
    (fun _ -> Request.emit signal)

(* -------------------------------------------------------------------------- *)
(* --- Marker Utilities                                                   --- *)
(* -------------------------------------------------------------------------- *)

let next_steps s =
  match s.skind with
  | If (cond, _, _, _) -> [ `Then cond ; `Else cond ]
  | Instr (Set _ | Call _ | Local_init _) -> [ `After ]
  | Instr (Asm _ | Code_annot _)
  | Switch _ | Loop _ | Block _ | UnspecifiedSequence _
  | TryCatch _ | TryFinally _ | TryExcept _
  | Instr (Skip _) | Return _ | Break _ | Continue _ | Goto _ | Throw _ -> []

let probe_stmt s =
  match s.skind with
  | Instr (Set(lv,_,_)) -> Some (Plval (lv,s))
  | Instr (Call(Some lr,_,_,_)) -> Some (Plval (lr,s))
  | Instr (Local_init(v,_,_)) -> Some (Plval ((Var v,NoOffset), s))
  | Return (Some e,_) | If(e,_,_,_) | Switch(e,_,_,_) -> Some (Pexpr (e,s))
  | _ -> None

let probe marker =
  let open Printer_tag in
  match marker with
  | PLval (_, _, (Var vi, NoOffset)) when Cil.isFunctionType vi.vtype -> None
  | PLval(_,Kstmt s,l) -> Some (Plval (l,s))
  | PExp(_,Kstmt s,e) -> Some (Pexpr (e,s))
  | PStmt(_,s) | PStmtStart(_,s) -> probe_stmt s
  | PVDecl(_,Kstmt s,v) -> Some (Plval ((Var v,NoOffset),s))
  | _ -> None

(* -------------------------------------------------------------------------- *)
(* --- Stmt Ranking                                                       --- *)
(* -------------------------------------------------------------------------- *)

module type Ranking_sig = sig
  val stmt : stmt -> int
  val sort : callstack list -> callstack list
end

module Ranking : Ranking_sig = struct

  class ranker = object(self)
    inherit Visitor.frama_c_inplace
    (* ranks really starts at 1 *)
    (* rank < 0 means not computed yet *)
    val mutable rank = (-1)
    val rmap = Smap.create 0
    val fmark = Kmap.create 0
    val fqueue = Queue.create ()

    method private call kf =
      if not (Kmap.mem fmark kf) then
        ( Kmap.add fmark kf () ; Queue.push kf fqueue )

    method private newrank s =
      let r = succ rank in
      Smap.add rmap s r ;
      rank <- r ; r

    method! vlval lv =
      begin
        try match fst lv with
          | Var vi -> self#call (Globals.Functions.get vi)
          | _ -> ()
        with Not_found -> ()
      end ; Cil.DoChildren

    method! vstmt_aux s =
      ignore (self#newrank s) ;
      Cil.DoChildren

    method flush =
      while not (Queue.is_empty fqueue) do
        let kf = Queue.pop fqueue in
        ignore (Visitor.(visitFramacKf (self :> frama_c_visitor) kf))
      done

    method compute =
      match Globals.entry_point () with
      | kf , _ -> self#call kf ; self#flush
      | exception Globals.No_such_entry_point _ -> ()

    method rank s =
      if rank < 0 then (rank <- 0 ; self#compute) ;
      try Smap.find rmap s
      with Not_found ->
        let kf = Kernel_function.find_englobing_kf s in
        self#call kf ;
        self#flush ;
        try Smap.find rmap s
        with Not_found -> self#newrank s

  end

  let stmt = let rk = new ranker in rk#rank

  let rec ranks (rks : int list) (cs : callstack) : int list =
    match cs with
    | [] -> rks
    | (_,Kglobal)::wcs -> ranks rks wcs
    | (_,Kstmt s)::wcs -> ranks (stmt s :: rks) wcs

  let order : int list -> int list -> int = Stdlib.compare

  let sort (wcs : callstack list) : callstack list =
    List.map fst @@
    List.sort (fun (_,rp) (_,rq) -> order rp rq) @@
    List.map (fun cs -> cs , ranks [] cs) wcs

end

(* -------------------------------------------------------------------------- *)
(* --- Domain Utilities                                                   --- *)
(* -------------------------------------------------------------------------- *)

module Jcallstack : S with type t = callstack = struct
  module I = Data.Index
      (Value_types.Callstack.Map)
      (struct let name = "eva-callstack-id" end)
  let jtype = Data.declare ~package ~name:"callstack" I.jtype
  type t = I.t
  let to_json = I.to_json
  let of_json = I.of_json
end

module Jcalls : Request.Output with type t = callstack = struct

  type t = callstack

  let jtype = Package.(Jlist (Jrecord [
      "callee" , Jkf.jtype ;
      "caller" , Joption Jkf.jtype ;
      "stmt" , Joption Jstmt.jtype ;
      "rank" , Joption Jnumber ;
    ]))

  let rec jcallstack jcallee ki cs : json list =
    match ki , cs with
    | Kglobal , _ | _ , [] -> [ `Assoc [ "callee", jcallee ] ]
    | Kstmt stmt , (called,ki) :: cs ->
      let jcaller = Jkf.to_json called in
      let callsite = `Assoc [
          "callee", jcallee ;
          "caller", jcaller ;
          "stmt", Jstmt.to_json stmt ;
          "rank", Jint.to_json (Ranking.stmt stmt) ;
        ]
      in
      callsite :: jcallstack jcaller ki cs

  let to_json = function
    | [] -> `List []
    | (callee,ki)::cs -> `List (jcallstack (Jkf.to_json callee) ki cs)

end

module Jtruth : Data.S with type t = truth = struct
  type t = truth
  let jtype = Package.(Junion [ Jtag "True" ; Jtag "False" ; Jtag "Unknown" ])
  let to_json = function
    | Abstract_interp.Unknown -> `String "Unknown"
    | True -> `String "True"
    | False -> `String "False"
  let of_json = function
    | `String "True" -> Abstract_interp.True
    | `String "False" -> Abstract_interp.False
    | _ -> Abstract_interp.Unknown
end

(* -------------------------------------------------------------------------- *)
(* --- Utility functions for cvalue and offsetmaps                        --- *)
(* -------------------------------------------------------------------------- *)

type offsetmap =
  | Offsetmap of Cvalue.V_Offsetmap.t
  | Bottom | Empty | Top | InvalidLoc

let pp_offsetmap typ fmt = function
  | Bottom -> Format.fprintf fmt "<BOTTOM>"
  | Empty -> Format.fprintf fmt "<EMPTY>"
  | Top -> Format.fprintf fmt "<NO INFORMATION>"
  | InvalidLoc -> Format.fprintf fmt "<INVALID LOCATION>"
  | Offsetmap offsm ->
    Cvalue.V_Offsetmap.pretty_generic ~typ () fmt offsm ;
    Eval_op.pretty_stitched_offsetmap fmt typ offsm

let extract_single_var vi state =
  let b = Base.of_varinfo vi in
  try
    match Cvalue.Model.find_base b state with
    | `Bottom -> Bottom
    | `Value m -> Offsetmap m
    | `Top -> Top
  with Not_found -> InvalidLoc

let reduce_loc_and_eval state loc =
  if Cvalue.Model.is_top state then Top
  else if not (Cvalue.Model.is_reachable state) then Bottom
  else if Int_Base.(equal loc.Locations.size zero) then Empty
  else
    let loc' = Locations.(valid_part Read loc) in
    if Locations.is_bottom_loc loc' then InvalidLoc
    else
      try
        let size = Int_Base.project loc'.Locations.size in
        match Cvalue.Model.copy_offsetmap loc'.Locations.loc size state with
        | `Bottom -> InvalidLoc
        | `Value offsm -> Offsetmap offsm
      with Abstract_interp.Error_Top -> Top

let find_offsetmap cvalue_state precise_loc =
  let f loc acc =
    match acc, reduce_loc_and_eval cvalue_state loc with
    | Offsetmap o1, Offsetmap o2 -> Offsetmap (Cvalue.V_Offsetmap.join o1 o2)
    | Bottom, v | v, Bottom -> v
    | Empty, v | v, Empty -> v
    | Top, Top -> Top
    | InvalidLoc, InvalidLoc -> InvalidLoc
    | InvalidLoc, (Offsetmap _ as res) -> res
    | Offsetmap _, InvalidLoc -> acc
    | Top, r | r, Top -> r (* cannot happen, we should get Top everywhere *)
  in
  Precise_locs.fold f precise_loc Bottom

(* Get pointed bases from a cvalue. *)
let get_bases cvalue =
  try Base.SetLattice.project (Cvalue.V.get_bases cvalue)
  with Abstract_interp.Error_Top -> Base.Hptset.empty

(* Get pointed bases from an offsetmap.  *)
let get_pointed_bases = function
  | Offsetmap offsm ->
    let get_bases v = Cvalue.V_Or_Uninitialized.get_v v |> get_bases in
    let f v acc = get_bases v |> Base.Hptset.union acc in
    Cvalue.V_Offsetmap.fold_on_values f offsm Base.Hptset.empty
  | Bottom | Empty | Top | InvalidLoc -> Base.Hptset.empty

(* Only keep a list of C variables from both previous functions. *)
let filter_variables bases =
  let add_var base acc =
    try Base.to_varinfo base :: acc
    with Base.Not_a_C_variable -> acc
  in
  let vars = List.rev (Base.Hptset.fold add_var bases []) in
  List.filter (fun vi -> not (Cil.isFunctionType vi.vtype)) vars

(* -------------------------------------------------------------------------- *)
(* --- EVA Proxy                                                          --- *)
(* -------------------------------------------------------------------------- *)

module type EvaProxy = sig
  val callstacks : stmt -> callstack list
  val evaluate : probe -> callstack option -> evaluations
end

module Proxy(A : Analysis.S) : EvaProxy = struct

  open Eval
  type dstate = A.Dom.state or_top_bottom

  let get_precise_loc =
    let default = fun _ -> Precise_locs.loc_top in
    Option.value ~default (A.Loc.get Main_locations.PLoc.key)

  let get_cvalue =
    let default = fun _ -> Cvalue.V.top in
    Option.value ~default (A.Val.get Main_values.CVal.key)

  let callstacks stmt =
    match A.get_stmt_state_by_callstack ~after:false stmt with
    | `Top | `Bottom -> []
    | `Value states -> CSmap.fold_sorted (fun cs _ wcs -> cs :: wcs) states []

  let dstate ~after stmt = function
    | None -> (A.get_stmt_state ~after stmt :> dstate)
    | Some cs ->
      match A.get_stmt_state_by_callstack ~selection:[cs] ~after stmt with
      | (`Top | `Bottom) as res -> res
      | `Value cmap ->
        try `Value (CSmap.find cmap cs)
        with Not_found -> `Bottom

  (* --- Converts an evaluation [result] into an exported [value]. ---------- *)

  (* Result of an evaluation: a generic value for scalar types, or an offsetmap
     for struct and arrays. *)
  type result =
    | Value of A.Val.t
    | Offsetmap of offsetmap

  let pp_result typ fmt = function
    | Value v -> A.Val.pretty fmt v
    | Offsetmap offsm -> pp_offsetmap typ fmt offsm

  let get_pointed_bases = function
    | Value v -> get_bases (get_cvalue v)
    | Offsetmap offsm -> get_pointed_bases offsm

  let get_pointed_markers stmt result =
    let bases = get_pointed_bases result in
    let vars = filter_variables bases in
    let kf =
      try Some (Kernel_function.find_englobing_kf stmt)
      with Not_found -> None
    in
    let to_marker vi =
      let text = Pretty_utils.to_string Printer.pp_varinfo vi in
      let marker = Printer_tag.PLval (kf, Kstmt stmt, Cil.var vi) in
      text, marker
    in
    List.map to_marker vars

  (* Creates an exported [value] from an evaluation result. *)
  let make_value typ stmt (result, alarms) =
    let descr = Format.asprintf "@[<hov 2>%a@]" Alarms.pretty in
    let f alarm status acc = (status, descr alarm) :: acc in
    let alarms = Alarmset.fold f [] alarms |> List.rev in
    let pretty_eval = Bottom.pretty (pp_result typ) in
    let value = Pretty_utils.to_string pretty_eval result in
    let pointed_markers = get_pointed_markers stmt in
    let pointed_vars = Bottom.fold ~bottom:[] pointed_markers result in
    { value; alarms; pointed_vars }

  (* --- Evaluates an expression or lvalue into an evaluation [result]. ----- *)

  let lval_to_offsetmap lval state =
    let cvalue_state = A.Dom.get_cvalue_or_top state in
    match lval with
    | Var vi, NoOffset ->
      let r = extract_single_var vi cvalue_state in
      `Value r, Alarmset.none
    | _ ->
      A.eval_lval_to_loc state lval >>=: fun loc ->
      let precise_loc = get_precise_loc loc in
      find_offsetmap cvalue_state precise_loc

  let eval_lval lval state =
    match Cil.(unrollType (typeOfLval lval)) with
    | TInt _ | TEnum _ | TPtr _ | TFloat _ ->
      A.copy_lvalue state lval >>=. fun value ->
      value.v >>-: fun v -> Value v
    | _ ->
      lval_to_offsetmap lval state >>=: fun offsm -> Offsetmap offsm

  let eval_expr expr state =
    A.eval_expr state expr >>=: fun value -> Value value

  (* --- Evaluates all steps (before/after the statement). ------------------ *)

  let do_next eval state stmt callstack =
    match stmt.skind with
    | If (cond, _, _, _) ->
      let then_state = (A.assume_cond stmt state cond true :> dstate) in
      let else_state = (A.assume_cond stmt state cond false :> dstate) in
      Cond (eval then_state, eval else_state)
    | Instr (Set _ | Call _ | Local_init _) ->
      let after_state = dstate ~after:true stmt callstack in
      After (eval after_state)
    | _ -> Nothing

  let eval_steps typ eval stmt callstack =
    let default value = { value; alarms = []; pointed_vars = []; } in
    let eval = function
      | `Bottom -> default "Unreachable"
      | `Top -> default "No information"
      | `Value state -> make_value typ stmt (eval state)
    in
    let before = dstate ~after:false stmt callstack in
    let here = eval before in
    let next =
      match before with
      | `Bottom | `Top -> Nothing
      | `Value state -> do_next eval state stmt callstack
    in
    { here; next; }

  let evaluate p callstack =
    match p with
    | Plval (lval, stmt) ->
      eval_steps (Cil.typeOfLval lval) (eval_lval lval) stmt callstack
    | Pexpr (expr, stmt) ->
      eval_steps (Cil.typeOf expr) (eval_expr expr) stmt callstack
end

let proxy =
  let make (a : (module Analysis.S)) = (module Proxy(val a) : EvaProxy) in
  let current = ref (make @@ Analysis.current_analyzer ()) in
  let hook a = current := make a ; Request.emit signal in
  Analysis.register_hook hook ;
  fun () -> !current

(* -------------------------------------------------------------------------- *)
(* --- Request getCallstacks                                              --- *)
(* -------------------------------------------------------------------------- *)

let () =
  Request.register ~package
    ~kind:`GET ~name:"getCallstacks"
    ~descr:(Md.plain "Callstacks for markers")
    ~input:(module Jlist(Jmarker))
    ~output:(module Jlist(Jcallstack))
    begin fun markers ->
      let module A : EvaProxy = (val proxy ()) in
      let add stmt = List.fold_right CSet.add (A.callstacks stmt) in
      let gather_callstacks cset marker =
        match probe marker with
        | Some (Pexpr (_, stmt) | Plval (_, stmt)) -> add stmt cset
        | None -> cset
      in
      let cset = List.fold_left gather_callstacks CSet.empty markers in
      Ranking.sort (CSet.elements cset)
    end

(* -------------------------------------------------------------------------- *)
(* --- Request getCallstackInfo                                           --- *)
(* -------------------------------------------------------------------------- *)

let () =
  Request.register ~package
    ~kind:`GET ~name:"getCallstackInfo"
    ~descr:(Md.plain "Callstack Description")
    ~input:(module Jcallstack)
    ~output:(module Jcalls)
    begin fun cs -> cs end

(* -------------------------------------------------------------------------- *)
(* --- Request getStmtInfo                                                --- *)
(* -------------------------------------------------------------------------- *)

let () =
  let getStmtInfo = Request.signature ~input:(module Jstmt) () in
  let set_fct = Request.result getStmtInfo ~name:"fct"
      ~descr:(Md.plain "Englobing function")
      (module Jkf)
  and set_rank = Request.result getStmtInfo ~name:"rank"
      ~descr:(Md.plain "Global stmt order")
      (module Jint)
  in
  Request.register_sig ~package getStmtInfo
    ~kind:`GET ~name:"getStmtInfo"
    ~descr:(Md.plain "Stmt Information")
    begin fun rq s ->
      set_fct rq (Kernel_function.find_englobing_kf s) ;
      set_rank rq (Ranking.stmt s) ;
    end

(* -------------------------------------------------------------------------- *)
(* --- Request getProbeInfo                                               --- *)
(* -------------------------------------------------------------------------- *)

let () =
  let getProbeInfo = Request.signature ~input:(module Jmarker) () in
  let set_evaluable = Request.result getProbeInfo
      ~name:"evaluable" ~descr:(Md.plain "Can the probe be evaluated?")
      (module Jbool)
  and set_code = Request.result_opt getProbeInfo
      ~name:"code" ~descr:(Md.plain "Probe source code")
      (module Jstring)
  and set_stmt = Request.result_opt getProbeInfo
      ~name:"stmt" ~descr:(Md.plain "Probe statement")
      (module Jstmt)
  and set_rank = Request.result getProbeInfo
      ~name:"rank" ~descr:(Md.plain "Probe statement rank")
      ~default:0 (module Jint)
  and set_effects = Request.result getProbeInfo
      ~name:"effects" ~descr:(Md.plain "Effectfull statement")
      ~default:false (module Jbool)
  and set_condition = Request.result getProbeInfo
      ~name:"condition" ~descr:(Md.plain "Conditional statement")
      ~default:false (module Jbool)
  in
  let set_probe rq pp p s =
    let computed = Analysis.is_computed () in
    let reachable = Results.is_reachable s in
    set_evaluable rq (computed && reachable);
    set_code rq (Some (Pretty_utils.to_string pp p)) ;
    set_stmt rq (Some s) ;
    set_rank rq (Ranking.stmt s) ;
    let on_steps = function
      | `Here -> ()
      | `Then _ | `Else _ -> set_condition rq true
      | `After -> set_effects rq true
    in List.iter on_steps (next_steps s)
  in
  Request.register_sig ~package getProbeInfo
    ~kind:`GET ~name:"getProbeInfo"
    ~descr:(Md.plain "Probe informations")
    begin fun rq marker ->
      match probe marker with
      | Some (Plval (l, s)) -> set_probe rq Printer.pp_lval l s
      | Some (Pexpr (e, s)) -> set_probe rq Printer.pp_exp  e s
      | None -> set_evaluable rq false
    end

(* -------------------------------------------------------------------------- *)
(* --- Request getValues                                                  --- *)
(* -------------------------------------------------------------------------- *)

module JEvaluation = struct
  open Server.Data

  type record
  let record: record Record.signature = Record.signature ()

  let value = Record.field record ~name:"value"
      ~descr:(Markdown.plain "Textual representation of the value")
      (module Data.Jstring)
  let alarms = Record.field record ~name:"alarms"
      ~descr:(Markdown.plain "Alarms raised by the evaluation")
      (module Jlist (Jpair (Jtruth) (Jstring)))
  let pointed_vars = Record.field record ~name:"pointedVars"
      ~descr:(Markdown.plain "List of variables pointed by the value")
      (module Jlist (Jpair (Jstring) (Jmarker)))

  let data = Record.publish record ~package ~name:"evaluation"
      ~descr:(Markdown.plain "Evaluation of an expression or lvalue")

  module R: Record.S with type r = record = (val data)
  type t = evaluation
  let jtype = R.jtype

  let to_json t =
    R.default |>
    R.set value t.value |>
    R.set alarms t.alarms |>
    R.set pointed_vars t.pointed_vars |>
    R.to_json
end

let () =
  let getValues = Request.signature () in
  let get_tgt = Request.param getValues ~name:"target"
      ~descr:(Md.plain "Works with all markers containing an expression")
      (module Jmarker)
  and get_cs = Request.param_opt getValues ~name:"callstack"
      ~descr:(Md.plain "Callstack to collect (defaults to none)")
      (module Jcallstack)
  and set_before = Request.result_opt getValues ~name:"vBefore"
      ~descr:(Md.plain "Domain values before execution")
      (module JEvaluation)
  and set_after = Request.result_opt getValues ~name:"vAfter"
      ~descr:(Md.plain "Domain values after execution")
      (module JEvaluation)
  and set_then = Request.result_opt getValues ~name:"vThen"
      ~descr:(Md.plain "Domain values for true condition")
      (module JEvaluation)
  and set_else = Request.result_opt getValues ~name:"vElse"
      ~descr:(Md.plain "Domain values for false condition")
      (module JEvaluation)
  in
  Request.register_sig ~package getValues
    ~kind:`GET ~name:"getValues"
    ~descr:(Md.plain "Abstract values for the given marker")
    begin fun rq () ->
      let module A : EvaProxy = (val proxy ()) in
      let marker = get_tgt rq and callstack = get_cs rq in
      match probe marker with
      | None -> ()
      | Some probe ->
        let domain = A.evaluate probe callstack in
        set_before rq (Some domain.here);
        match domain.next with
        | After value -> set_after rq (Some value)
        | Cond (v_then, v_else) ->
          set_then rq (Some v_then);
          set_else rq (Some v_else)
        | Nothing -> ()
    end

(* -------------------------------------------------------------------------- *)
