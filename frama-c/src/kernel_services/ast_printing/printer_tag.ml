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
(* --- Localizable API                                                    --- *)
(* -------------------------------------------------------------------------- *)

open Cil_types
open Cil_datatype

type localizable =
  | PStmt of (kernel_function * stmt)
  | PStmtStart of (kernel_function * stmt)
  | PLval of (kernel_function option * kinstr * lval)
  | PExp of (kernel_function option * kinstr * exp)
  | PTermLval of (kernel_function option * kinstr * Property.t * term_lval)
  | PVDecl of (kernel_function option * kinstr * varinfo)
  | PGlobal of global
  | PIP of Property.t

let glabel = function
  | GType(tinfo,_) -> tinfo.tname
  | GCompTag(comp, _) | GCompTagDecl(comp, _) -> comp.cname
  | GEnumTag(enum, _) | GEnumTagDecl(enum, _) -> enum.ename
  | GVarDecl(vi,_) | GVar(vi, _, _)
  | GFun( { svar=vi }, _) | GFunDecl(_,vi,_) -> vi.vname
  | GPragma((Attr(a,_) | AttrAnnot a),_) -> a
  | GAnnot _ -> "(annotation)"
  | GAsm _ -> "(assembly)"
  | GText _ -> "(text)"

let label = function
  | PVDecl(_,_,vi) -> vi.vname
  | PLval (_, _, (Var vi, NoOffset)) -> vi.vname
  | PLval _ -> "(l-value)"
  | PExp  _ -> "(expression)"
  | PStmt _ | PStmtStart _ -> "(statement)"
  | PTermLval _ -> "(term)"
  | PGlobal g -> glabel g
  | PIP _ -> "(property)"

let decl_of = function
  | GCompTag(comp,loc) -> GCompTagDecl(comp,loc)
  | GEnumTag(enum,loc) -> GEnumTagDecl(enum,loc)
  | GFunDecl(_,vi,loc) | GVar(vi,_,loc) | GFun({ svar=vi },loc)
    -> GVarDecl(vi,loc)
  | GAsm(_,loc) -> GAsm("…",loc)
  | GText s when String.length s > 20 -> GText(String.sub s 0 20 ^ "…")
  | GPragma(Attr(a,_),loc) -> GPragma(Attr(a,[]),loc)
  | GAnnot _ -> GText "Global annotation"
  | ( GType _ | GCompTagDecl _ | GEnumTagDecl _
    | GVarDecl _ | GText _ | GPragma _) as g -> g

let pretty fmt = function
  | PVDecl (_, _, vi) -> Printer.pp_vdecl fmt vi
  | PLval (_, _, lval) -> Printer.pp_lval fmt lval
  | PExp  (_, _, expr) -> Printer.pp_exp fmt expr
  | PTermLval (_, _, _, lv) -> Printer.pp_term_lval fmt lv
  | PIP prop -> Description.pp_property fmt prop
  | PGlobal g -> Printer.pp_global fmt (decl_of g)
  | PStmt(_,stmt) | PStmtStart (_, stmt) ->
    Printer.(without_annot pp_stmt) fmt stmt

let pp_ki_loc fmt ki =
  match ki with
  | Kglobal -> (* no location, print 'global' *)
    Format.fprintf fmt "global"
  | Kstmt st -> Filepath.pp_pos fmt (fst @@ Stmt.loc st)

let pp_debug fmt = function
  | PStmtStart (_, s) ->
    Format.fprintf fmt "LocalizableStart %d (%a)"
      s.sid Printer.pp_location (Cil_datatype.Stmt.loc s)
  | PStmt (_, s) ->
    Format.fprintf fmt "LocalizableStmt %d (%a)"
      s.sid Printer.pp_location (Cil_datatype.Stmt.loc s)
  | PLval (_, ki, lv) ->
    Format.fprintf fmt "LocalizableLval %a (%a)"
      Printer.pp_lval lv pp_ki_loc ki
  | PExp (_, ki, lv) ->
    Format.fprintf fmt "LocalizableExp %a (%a)"
      Printer.pp_exp lv pp_ki_loc ki
  | PTermLval (_, ki, _pi, tlv) ->
    Format.fprintf fmt "LocalizableTermLval %a (%a)"
      Printer.pp_term_lval tlv pp_ki_loc ki
  | PVDecl (_, _, vi) ->
    Format.fprintf fmt "LocalizableVDecl %a" Printer.pp_vdecl vi
  | PGlobal g ->
    Format.fprintf fmt "LocalizableGlobal %a" Printer.pp_global g
  | PIP ip ->
    Format.fprintf fmt "LocalizableIP %a" Description.pp_property ip

module Localizable =
  Datatype.Make_with_collections
    (struct
      include Datatype.Undefined
      type t = localizable

      let name = "Printer_tag.Localizable"
      let reprs = List.map (fun g -> PGlobal g) Global.reprs
      let mem_project = Datatype.never_any_project

      let hash = function
        | PStmtStart (_,s) ->
          Hashtbl.hash( 0, Stmt.hash s )
        | PStmt (_,s) ->
          Hashtbl.hash( 1, Stmt.hash s )
        | PLval (_,ki,lv) ->
          Hashtbl.hash( 2, Kinstr.hash ki, Lval.hash lv )
        | PTermLval(_,ki,pi,lv) ->
          Hashtbl.hash( 3, Kinstr.hash ki, Property.hash pi, Term_lval.hash lv)
        | PVDecl(_,_,v) ->
          Hashtbl.hash( 4, Varinfo.hash v )
        | PExp(_,_,e) ->
          Hashtbl.hash( 5, Exp.hash e )
        | PIP ip ->
          Hashtbl.hash( 6, Property.hash ip )
        | PGlobal g ->
          Hashtbl.hash( 7, Global.hash g )

      let equal l1 l2 = match l1,l2 with
        | PStmt (_,ki1), PStmt (_,ki2) -> ki1.sid = ki2.sid
        | PStmtStart (_,ki1), PStmtStart (_,ki2) -> ki1.sid = ki2.sid
        | PLval (_,ki1,lv1), PLval (_,ki2,lv2) ->
          Kinstr.equal ki1 ki2 &&
          Lval.equal lv1 lv2
        | PTermLval (_,ki1,pi1,lv1), PTermLval (_,ki2,pi2,lv2) ->
          Kinstr.equal ki1 ki2 &&
          Property.equal pi1 pi2 &&
          Term_lval.equal lv1 lv2
        | PVDecl (_,_,v1), PVDecl (_,_,v2) -> Varinfo.equal v1 v2
        | PExp (_,_,e1), PExp(_,_,e2) -> Exp.equal e1 e2
        | PIP ip1, PIP ip2 -> Property.equal ip1 ip2
        | PGlobal g1, PGlobal g2 -> Global.equal g1 g2
        | (PStmt _ | PStmtStart _ | PLval _ | PExp _ | PTermLval _ | PVDecl _
          | PIP _ | PGlobal _), _
          ->  false

      let compare l1 l2 = match l1,l2 with
        | PStmt(_,s1) , PStmt(_,s2) -> Stmt.compare s1 s2
        | PStmt _ , _ -> (-1)
        | _ , PStmt _ -> 1
        | PStmtStart(_,s1) , PStmtStart(_,s2) -> Stmt.compare s1 s2
        | PStmtStart _ , _ -> (-1)
        | _ , PStmtStart _ -> 1
        | PLval (_,k1,lv1), PLval(_,k2,lv2) ->
          let cmp = Kinstr.compare k1 k2 in
          if cmp<>0 then cmp else Lval.compare lv1 lv2
        | PLval _ , _ -> (-1)
        | _ , PLval _ -> 1
        | PTermLval(_,k1,p1,lv1) , PTermLval(_,k2,p2,lv2) ->
          let cmp = Kinstr.compare k1 k2 in
          if cmp<>0 then cmp else
            let cmp = Property.compare p1 p2 in
            if cmp<>0 then cmp else
              Term_lval.compare lv1 lv2
        | PTermLval _ , _ -> (-1)
        | _ , PTermLval _ -> 1
        | PVDecl(_,_,v1) , PVDecl(_,_,v2) -> Varinfo.compare v1 v2
        | PVDecl _ , _ -> (-1)
        | _ , PVDecl _ -> 1
        | PExp(_,_,e1) , PExp(_,_,e2) -> Exp.compare e1 e2
        | PExp _ , _ -> (-1)
        | _ , PExp _ -> 1
        | PIP p1 , PIP p2 -> Property.compare p1 p2
        | PIP _ , _ -> (-1)
        | _ , PIP _ -> 1
        | PGlobal g1 , PGlobal g2 -> Global.compare g1 g2

      let pretty = pretty (* defined above *)

    end)

(* -------------------------------------------------------------------------- *)
(* --- Utility Accessors                                                  --- *)
(* -------------------------------------------------------------------------- *)

let kf_of_localizable loc =
  match loc with
  | PLval (kf_opt, _, _)
  | PExp (kf_opt,_,_)
  | PTermLval(kf_opt, _,_,_)
  | PVDecl (kf_opt, _, _) -> kf_opt
  | PStmt (kf, _) | PStmtStart(kf,_) -> Some kf
  | PIP ip -> Property.get_kf ip
  | PGlobal (GFun ({svar = vi}, _)) -> Some (Globals.Functions.get vi)
  | PGlobal _ -> None

let ki_of_localizable loc = match loc with
  | PLval (_, ki, _)
  | PExp (_, ki, _)
  | PTermLval(_, ki,_,_)
  | PVDecl (_, ki, _) -> ki
  | PStmt (_, st) | PStmtStart(_, st) -> Kstmt st
  | PIP ip -> Property.get_kinstr ip
  | PGlobal _ -> Kglobal

let varinfo_of_localizable = function
  | PLval (_, _, (Var vi, NoOffset)) -> Some vi
  | PVDecl (_, _, vi) -> Some vi
  | PGlobal (GVar (vi, _, _) | GVarDecl (vi, _)
            | GFunDecl (_, vi, _) | GFun ({svar = vi }, _)) -> Some vi
  | _ -> None

let typ_of_localizable = function
  | PLval (_, _, lval) -> Some (Cil.typeOfLval lval)
  | PExp (_, _, expr) -> Some (Cil.typeOf expr)
  | _ -> None

let loc_of_localizable = function
  | PStmt (_,st) | PStmtStart(_,st)
  | PLval (_,Kstmt st,_) | PExp(_,Kstmt st, _)
  | PTermLval(_,Kstmt st,_,_) ->
    Stmt.loc st
  | PIP ip ->
    (match Property.get_kinstr ip with
     | Kglobal ->
       (match Property.get_kf ip with
          None -> Location.unknown
        | Some kf -> Kernel_function.get_location kf)
     | Kstmt st -> Stmt.loc st)
  | PVDecl (_,_,vi) -> vi.vdecl
  | PGlobal g -> Global.loc g
  | (PLval _ | PTermLval _ | PExp _) as localize ->
    (match kf_of_localizable localize with
     | None -> Location.unknown
     | Some kf -> Kernel_function.get_location kf)


(* -------------------------------------------------------------------------- *)
(* --- Helper for Globals                                                 --- *)
(* -------------------------------------------------------------------------- *)

let localizable_of_kf kf =
  let vi = Globals.Functions.get_vi kf in
  PVDecl(Some kf,Kglobal,vi)

let localizable_of_global g =
  match g with
  | GVarDecl(vi,_) | GVar(vi,_,_) when vi.vglob ->
    PVDecl(None,Kglobal,vi)
  | GFun({ svar = vi },_) | GFunDecl(_,vi,_) ->
    (try PVDecl(Some (Globals.Functions.get vi) , Kglobal, vi)
     with Not_found -> PGlobal g)
  | _ -> PGlobal g

(* -------------------------------------------------------------------------- *)
(* --- Find localizable at a Filepath.position                            --- *)
(* -------------------------------------------------------------------------- *)

let dkey = Kernel.register_category "pretty-source"

module LineToLocalizable =
  Datatype.Hashtbl(Datatype.Int.Hashtbl)(Datatype.Int)
    (struct let module_name = "Pretty_source.LineToLocalizable" end)
module FileToLines =
  Datatype.Hashtbl(Datatype.Filepath.Hashtbl)(Datatype.Filepath)
    (struct let module_name = "Pretty_source.FilesToLine" end)

module MappingLineLocalizable = struct
  module LineToLocalizableAux =
    LineToLocalizable.Make( Datatype.Pair(Location)(Localizable))

  include State_builder.Hashtbl(FileToLines)(LineToLocalizableAux)
      (struct
        let size = 5
        let dependencies = [Ast.self]
        let name = "Pretty_source.line_to_localizable"
      end)
end

class pos_to_localizable =
  object (self)
    inherit Visitor.frama_c_inplace

    (* used to keep track of conditional expressions, to add them to the
       list of relevant localizables *)
    val mutable insideIf = None

    method add_range loc (localizable : localizable) =
      if not (Location.equal loc Location.unknown) then (
        let p1, p2 = loc in
        if p1.Filepath.pos_path <> p2.Filepath.pos_path then
          Kernel.debug ~once:true ~dkey
            "Localizable over two files: %a and %a; %a"
            Datatype.Filepath.pretty p1.Filepath.pos_path
            Datatype.Filepath.pretty p2.Filepath.pos_path
            Localizable.pretty localizable;
        let file = p1.Filepath.pos_path in
        let hfile =
          try MappingLineLocalizable.find file
          with Not_found ->
            let h = LineToLocalizable.create 17 in
            MappingLineLocalizable.add file h;
            h
        in
        for i = p1.Filepath.pos_lnum to p2.Filepath.pos_lnum do
          LineToLocalizable.add hfile i (loc, localizable);
        done
      );

    method! vstmt_aux s =
      (* we ignore Block statements, since they tend to overlap existing
         ones which are more precise *)
      let skip = match s.skind with
        | Block _ -> true
        | _ -> false
      in
      if not skip then
        self#add_range (Stmt.loc s) (PStmt (Option.get self#current_kf, s));
      begin
        match s.skind with
        | If (exp, _, _, _) ->
          (* conditional expressions are treated in a special way *)
          insideIf <- Some (Kstmt s);
          ignore (Cil.visitCilExpr (self :> Cil.cilVisitor) exp);
          insideIf <- None
        | _ -> ()
      end;
      Cil.DoChildren

    method! vexpr exp =
      begin
        match insideIf with
        | Some ki ->
          (* expressions inside conditionals have a special treatment *)
          begin
            match exp.enode with
            | Lval lv ->
              (* lvals must be generated differently from other expressions *)
              self#add_range exp.eloc (PLval(self#current_kf, ki, lv))
            | _ ->
              self#add_range exp.eloc (PExp(self#current_kf, ki, exp))
          end
        | None -> ()
      end;
      Cil.DoChildren

    method! vvdec vi =
      if not vi.vglob && not vi.vtemp then
        begin
          match self#current_kf with
          | None -> (* should not happen*) ()
          | Some kf ->
            self#add_range vi.vdecl (PVDecl (Some kf,self#current_kinstr,vi));
        end;
      Cil.DoChildren

    method! vglob_aux g =
      (match g with
       | GFun ({ svar = vi }, loc) ->
         self#add_range loc
           (PVDecl (Some (Globals.Functions.get vi), Kglobal, vi))
       | GVar (vi, _, loc) ->
         self#add_range loc (PVDecl (None, Kglobal, vi))
       | GFunDecl (_, vi, loc) ->
         self#add_range loc
           (PVDecl (Some (Globals.Functions.get vi), Kglobal, vi))
       | GVarDecl (vi, loc) ->
         self#add_range loc (PVDecl (None, Kglobal, vi))
       | _ -> self#add_range (Global.loc g) (PGlobal g)
      );
      Cil.DoChildren
  end

(* Returns [true] if the column [col] is within location [loc]. *)
let location_contains_col loc col =
  let (pos_start, pos_end) = loc in
  let (col_start, col_end) =
    pos_start.Filepath.pos_cnum - pos_start.Filepath.pos_bol,
    pos_end.Filepath.pos_cnum - pos_end.Filepath.pos_bol
  in
  col_start <= col && col <= col_end

(* Applies several heuristics to try and match the best localizable to a
   given location [loc]. The list [possible_locs] should contain all
   localizables in a given line. If [possible_col] is [true], then we try
   to take column information into account.
   Some heuristics may return an empty list, in which case a fallback is
   later used to return a better choice. *)
let apply_location_heuristics precise_col possible_locs loc =
  let col = loc.Filepath.pos_cnum - loc.Filepath.pos_bol in
  Kernel.debug ~dkey
    "apply_location_heuristics (precise_col:%b): loc: %a, col: %d@\n\
     possible_locs:@ %a"
    precise_col Location.pretty (loc, loc) col
    (Pretty_utils.pp_list ~sep:"@\n"
       (Pretty_utils.pp_pair ~sep:" :: " Location.pretty Localizable.pretty)) possible_locs;
  (* Heuristic 1: we try to obtain a subset of localizables related to a given
     position, or a given column if [precise_col] is true.
     May result in an empty list. *)
  let filter_locs l =
    List.filter (fun (((pos_start, _) as loc'), _) ->
        if precise_col then location_contains_col loc' col
        else loc = pos_start
      ) l
  in
  (* Heuristic 2: prioritize expressions if they are present.
     May result in an empty list. *)
  let exps l =
    List.filter (fun (_, lz) -> match lz with | PExp _ -> true | _ -> false) l
  in
  (* Heuristic 3: when we have more than one match with the exact same location,
     we pick the last one in the list. This will be the first statement that has
     been encountered, and this criterion seems to work well with temporaries
     introduced by Cil. *)
  let last l = match List.rev l with [] -> None | (_, lz) :: _ -> Some lz in
  (* Heuristic 4: when there are no exact locations, we will consider the
     innermost ones, that is, those at the top of the list. *)
  let innermost_in loc l =
    List.filter (fun (loc', _) -> Location.equal loc loc') l
  in
  match possible_locs, filter_locs possible_locs with
  | [], _ -> (* no possible localizables *) None
  | _, (_ :: _ as exact) ->
    (* one or more exact localizables; we prioritize expressions *)
    begin
      match exps exact with
      | [] -> (* no expressions, just take the last localizable *) last exact
      | exps -> (* take the last (usually only) expression *) last exps
    end
  | (loc', _) :: __, [] ->
    (* No exact loc. We consider the innermost statements,
       ie those at the top of the list *)
    let filtered = innermost_in loc' possible_locs in
    last filtered

let loc_to_localizable ?(precise_col=false) loc =
  if not (MappingLineLocalizable.is_computed ()) then (
    let vis = new pos_to_localizable in
    Visitor.visitFramacFile (vis :> Visitor.frama_c_visitor) (Ast.get ());
    MappingLineLocalizable.mark_as_computed ();
  );
  try
    (* Find the mapping from this file to locs-by-line *)
    let hfile = MappingLineLocalizable.find loc.Filepath.pos_path in
    (* Find the localizable for this line *)
    let all = LineToLocalizable.find_all hfile loc.Filepath.pos_lnum in
    match apply_location_heuristics precise_col all loc with
    | Some locz ->
      Kernel.feedback ~dkey "loc: %a -> locz: %a"
        Location.pretty (loc,loc) Localizable.pretty locz;
      Some locz
    | None ->
      Kernel.feedback ~dkey "loc: %a -> NO locz" Location.pretty (loc,loc);
      None
  with
  | Not_found ->
    Kernel.debug ~once:true ~source:loc "no matching localizable found";
    None

(* -------------------------------------------------------------------------- *)
(* --- Printer API                                                        --- *)
(* -------------------------------------------------------------------------- *)

module type TAG =
sig
  val create : localizable -> string
  val unfold : stmt -> bool
end

(* We delay the creation of the class to execution time, so that all
   pretty-printer extensions get properly registered (as we want to inherit
   from them). The only known solution is to use a functor *)
module BUILD(Tag : TAG)(X: Printer.PrinterClass) : Printer.PrinterClass =
struct

  class printer : Printer.extensible_printer = object(self)

    inherit X.printer as super

    val mutable current_property = None

    method private current_kinstr =
      match self#current_stmt with
      | None -> Kglobal
      | Some st -> Kstmt st

    method private current_sid =
      match super#current_stmt with
      | None -> assert false
      | Some st -> st.sid

    method private current_kf =
      match super#current_function with
      | None -> None
      | Some fd -> Some (Globals.Functions.get fd)

    val mutable current_ca = None

    val mutable active_behaviors = []

    method private current_behavior_or_loop =
      match current_ca with
        None ->
        let active = Datatype.String.Set.of_list active_behaviors in
        Property.Id_contract (active ,Option.get self#current_behavior)
      | Some ca -> Property.Id_loop ca

    (* When [stmt] is a call, this method "inlines" the preconditions of the
       functions that may be called here, with some context. This way,
       bullets are more precise, etc. *)
    method private preconditions_at_call fmt stmt =
      match stmt.skind with
      | Instr (Call _)
      | Instr (Local_init (_, ConsInit _, _)) ->
        let extract_instance_predicate = function
          | Property.IPPropertyInstance {Property.ii_pred} -> ii_pred
          (* Other cases should not happen, unless a plugin has replaced call
             preconditions. In this case, print nothing but do not crash. *)
          | _ -> raise Not_found
        in
        let extract_predicate = function
          | Property.IPPredicate {Property.ip_pred} -> ip_pred
          | _ -> assert false
        in
        (* Functons called at this point *)
        let called = Statuses_by_call.all_functions_with_preconditions stmt in
        let warn_missing = false in
        let add_by_kf kf acc =
          let ips =
            Statuses_by_call.all_call_preconditions_at ~warn_missing kf stmt
          in
          if ips = [] then acc else (kf, ips) :: acc
        in
        let ips_all_kfs = Kernel_function.Hptset.fold add_by_kf called [] in
        let pp_one fmt (original_p, p) =
          match extract_instance_predicate p with
          | Some pred -> Format.fprintf fmt "@[%a@]" self#requires_aux (p, pred)
          | None ->
            let pred = extract_predicate original_p in
            (* Makes the original predicate non clickable, as it may involve
               the formal parameters which are not in scope at the call site. *)
            Format.fprintf fmt "@[Non transposable: %s@]"
              (Format.asprintf "@[%a@]" self#requires_aux (original_p, pred))
          | exception Not_found -> ()
        in
        let pp_by_kf fmt (kf, ips) =
          Format.fprintf fmt "@[preconditions of %a:@]@ %a"
            Kernel_function.pretty kf
            (Pretty_utils.pp_list ~pre:"" ~sep:"@ " ~suf:"" pp_one) ips
        in
        if ips_all_kfs <> [] then
          Pretty_utils.pp_list ~pre:"@[<v 3>/* " ~sep:"@ " ~suf:" */@]@ "
            pp_by_kf fmt ips_all_kfs
      | _ -> ()


    method! next_stmt next fmt current =
      if Tag.unfold current
      then self#preconditions_at_call fmt current;
      Format.fprintf fmt "@{<%s>%a@}"
        (Tag.create (PStmt (Option.get self#current_kf,current)))
        (super#next_stmt next) current

    method! lval fmt lv =
      match self#current_kinstr with
      | Kglobal -> super#lval fmt lv
      (* Do not highlight the lvals in initializers. *)
      | Kstmt _ as ki ->
        Format.fprintf fmt "@{<%s>"
          (Tag.create (PLval (self#current_kf,ki,lv)));
        (match lv with
         | Var vi, (Field _| Index _ as o) ->
           (* Small hack to be able to click on the arrays themselves
              in the easy cases *)
           self#lval fmt (Var vi, NoOffset);
           self#offset fmt o
         | _ -> super#lval fmt lv
        );
        Format.fprintf fmt "@}"

    method! exp fmt e =
      match e.enode with
      | Lval lv ->
        (* Do not mark immediate l-values as they would not be
               selectable anyway because of the embedded tags of self#lval.
               This is only an optimization. *)
        self#lval fmt lv
      | _ ->
        Format.fprintf fmt "@{<%s>"
          (Tag.create (PExp (self#current_kf,self#current_kinstr,e)));
        super#exp fmt e;
        Format.fprintf fmt "@}"

    method! term_lval fmt lv =
      (* similar to pLval, except that term_lval can appear in specifications
         of functions (ki = None, kf <> None). Initializers are ignored. *)
      if self#current_kinstr = Kglobal && self#current_kf = None then begin
        super#term_lval fmt lv (* Do not highlight the lvals in initializers. *)
      end else begin
        match current_property with
        | None -> (* Also use default printer for this case (possible inside
                     pragmas, for example). *)
          super#term_lval fmt lv
        | Some ip ->
          Format.fprintf fmt "@{<%s>"
            (Tag.create
               (PTermLval (self#current_kf, self#current_kinstr, ip, lv)));
          (match lv with
           | TVar vi, (TField _| TIndex _ as o) ->
             self#term_lval fmt (TVar vi, TNoOffset);
             self#term_offset fmt o
           | _ -> super#term_lval fmt lv
          );
          Format.fprintf fmt "@}"
      end

    method! vdecl fmt vi =
      Format.fprintf fmt "@{<%s>%a@}"
        (Tag.create (PVDecl (self#current_kf, self#current_kinstr, vi)))
        super#vdecl vi

    method private tag_property p =
      current_property <- Some p;
      Tag.create (PIP p)

    method! code_annotation fmt ca =
      match ca.annot_content with
      | APragma p when not (Logic_utils.is_property_pragma p) ->
        (* Not currently localizable. Will be linked to the next stmt *)
        super#code_annotation fmt ca
      | AAssert _ | AInvariant _ | APragma _ | AVariant _ ->
        let ip =
          Property.ip_of_code_annot_single
            (Option.get self#current_kf)
            (Option.get self#current_stmt)
            ca
        in
        Format.fprintf fmt "@{<%s>%a@}"
          (self#tag_property ip)
          super#code_annotation ca;
      | AStmtSpec (active,_) | AExtended(active,_,_) ->
        (* tags will be set in the inner nodes. *)
        active_behaviors <- active;
        super#code_annotation fmt ca;
        active_behaviors <- [];
      | AAllocation _
      | AAssigns _  ->
        (* tags will be set in the inner nodes. *)
        current_ca <- Some ca;
        super#code_annotation fmt ca;
        current_ca <- None

    method! global fmt g =
      match g with
      (* these globals are already covered by PVDecl *)
      | GVarDecl _ | GVar _ | GFunDecl _ | GFun _ -> super#global fmt g
      | _ ->
        Format.fprintf fmt "@{<%s>%a@}"
          (Tag.create (PGlobal g))
          super#global
          g

    method! extended fmt ext =
      let loc =
        match self#current_kf with
        | None -> Property.ELGlob
        | Some kf -> Property.e_loc_of_stmt kf self#current_kinstr
      in
      Format.fprintf fmt "@{<%s>%a@}"
        (self#tag_property Property.(ip_of_extended loc ext))
        super#extended ext;

    method private requires_aux fmt (ip, p) =
      Format.fprintf fmt "@{<%s>%a@}"
        (self#tag_property ip)
        super#requires p;

    method! requires fmt p =
      let b = Option.get self#current_behavior in
      let ip =
        Property.ip_of_requires
          (Option.get self#current_kf) self#current_kinstr b p
      in
      self#requires_aux fmt (ip, p)

    method! behavior fmt b =
      Format.fprintf fmt "@{<%s>%a@}"
        (self#tag_property
           (Property.ip_of_behavior
              (Option.get self#current_kf)
              self#current_kinstr
              ~active:active_behaviors b))
        super#behavior b

    method! decreases fmt t =
      Format.fprintf fmt "@{<%s>%a@}"
        (self#tag_property
           (Property.ip_of_decreases
              (Option.get self#current_kf) self#current_kinstr t))
        super#decreases t;

    method! terminates fmt t =
      Format.fprintf fmt "@{<%s>%a@}"
        (self#tag_property
           (Property.ip_of_terminates
              (Option.get self#current_kf) self#current_kinstr t))
        super#terminates t;

    method! complete_behaviors fmt t =
      Format.fprintf fmt "@{<%s>%a@}"
        (self#tag_property
           (Property.ip_of_complete
              (Option.get self#current_kf)
              self#current_kinstr
              ~active:active_behaviors
              t))
        super#complete_behaviors t

    method! disjoint_behaviors fmt t =
      Format.fprintf fmt "@{<%s>%a@}"
        (self#tag_property
           (Property.ip_of_disjoint
              (Option.get self#current_kf)
              self#current_kinstr
              ~active:active_behaviors
              t))
        super#disjoint_behaviors t

    method! assumes fmt p =
      let b = Option.get self#current_behavior in
      Format.fprintf fmt "@{<%s>%a@}"
        (self#tag_property
           (Property.ip_of_assumes
              (Option.get self#current_kf) self#current_kinstr b p))
        super#assumes p;

    method! post_cond fmt pc =
      let b = Option.get self#current_behavior in
      Format.fprintf fmt "@{<%s>%a@}"
        (self#tag_property
           (Property.ip_of_ensures
              (Option.get self#current_kf) self#current_kinstr b pc))
        super#post_cond pc;

    method! assigns s fmt a =
      match
        Property.ip_of_assigns (Option.get self#current_kf) self#current_kinstr
          self#current_behavior_or_loop a
      with
        None -> super#assigns s fmt a
      | Some ip ->
        Format.fprintf fmt "@{<%s>%a@}"
          (self#tag_property ip) (super#assigns s) a

    method! from s fmt ((_, f) as from) =
      match f with
      | FromAny -> super#from s fmt from
      | From _ ->
        let ip =
          Option.get
            (Property.ip_of_from
               (Option.get self#current_kf) self#current_kinstr
               self#current_behavior_or_loop from)
        in
        Format.fprintf fmt "@{<%s>%a@}"
          (Tag.create (PIP ip)) (super#from s) from

    method! global_annotation fmt a =
      match Property.ip_of_global_annotation_single a with
      | None -> super#global_annotation fmt a
      | Some ip ->
        Format.fprintf fmt "@{<%s>%a@}"
          (Tag.create (PIP ip)) super#global_annotation a

    method! allocation ~isloop fmt a =
      match
        Property.ip_of_allocation (Option.get self#current_kf) self#current_kinstr
          self#current_behavior_or_loop a
      with
        None -> super#allocation ~isloop fmt a
      | Some ip ->
        Format.fprintf fmt "@{<%s>%a@}"
          (Tag.create (PIP ip)) (super#allocation ~isloop) a;

    method! stmtkind sattr next fmt sk =
      (* Special tag denoting the start of the statement, WITHOUT any ACSL
         assertion/statement contract, etc. *)
      let s = Option.get self#current_stmt in
      let f = Option.get self#current_kf in
      let tag = Tag.create (PStmtStart(f,s)) in
      Format.fprintf fmt "@{<%s>%a@}" tag (super#stmtkind sattr next) sk

    initializer force_brace <- true

  end
end

module type Tag =
sig
  val create : localizable -> string
end

module type S_pp =
sig
  include Printer_api.S_pp
  val with_unfold_precond : (stmt -> bool) ->
    (Format.formatter -> 'a -> unit) ->
    (Format.formatter -> 'a -> unit)
end

module Make(T : Tag) =
struct

  let unfold = ref (fun (_ : stmt) -> false)

  let printer () =
    let pp = Printer.current_printer () in
    let module PP = (val pp: Printer.PrinterClass) in
    let module TAG = struct
      let create = T.create
      let unfold s = !unfold s
    end in
    let module TagPrinterClass = BUILD(TAG)(PP) in
    new TagPrinterClass.printer

  let with_unfold_precond unfolder f fmt x =
    let stack = !unfold in
    try unfold := unfolder ; f fmt x ; unfold := stack
    with err -> unfold := stack ; raise err

  include Printer_builder.Make_pp(struct let printer = printer end)

end

(* -------------------------------------------------------------------------- *)
