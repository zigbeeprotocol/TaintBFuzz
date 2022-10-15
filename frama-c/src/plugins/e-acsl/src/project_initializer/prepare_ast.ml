(**************************************************************************)
(*                                                                        *)
(*  This file is part of the Frama-C's E-ACSL plug-in.                    *)
(*                                                                        *)
(*  Copyright (C) 2012-2021                                               *)
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

let dkey = Options.Dkey.prepare

(**************************************************************************)
(********************** Forward references ********************************)
(**************************************************************************)

let is_libc_writing_memory_ref: (varinfo -> bool) ref =
  Extlib.mk_fun "is_libc_writing_memory_ref"

(* ********************************************************************** *)
(* Environment *)
(* ********************************************************************** *)

module Dup_functions: sig
  val generate_vi: varinfo -> varinfo (* return the new varinfo *)
  val mem: varinfo -> bool
  val find: varinfo -> varinfo
  val reset: unit -> unit
end = struct

  let tbl: varinfo Varinfo.Hashtbl.t = Varinfo.Hashtbl.create 7

  (* assume [vi] is not already in [tbl] *)
  let generate_vi vi =
    let new_name = Functions.RTL.mk_gen_name vi.vname in
    let new_vi =
      Cil.makeGlobalVar
        ~referenced:vi.vreferenced
        ~loc:vi.vdecl
        new_name
        vi.vtype
    in
    Varinfo.Hashtbl.add tbl vi new_vi;
    new_vi

  let mem = Varinfo.Hashtbl.mem tbl
  let find = Varinfo.Hashtbl.find tbl
  let reset () = Varinfo.Hashtbl.clear tbl

end

(* ********************************************************************** *)
(* Duplicating a function *)
(* ********************************************************************** *)

(* [formals] associates the old formals to the new ones in order to
   substitute them in [spec]. *)
let dup_funspec formals spec =
  (*  Options.feedback "DUP SPEC %a" Cil.d_funspec spec;*)
  let o = object
    inherit Visitor.frama_c_refresh (Project.current ())

    val already_visited = Logic_var.Hashtbl.create 7

    (* just substituting in [!vvrbl] (when using a varinfo) does not work
       because varinfo's occurrences are shared in logic_vars, so modifying the
       varinfo would modify any logic_var based on it, even if it is not part of
       this [spec] (e.g., if it is in another annotation of the same
       function) *)
    method !vlogic_var_use orig_lvi =
      match orig_lvi.lv_origin with
      | None ->
        Cil.JustCopy
      | Some vi ->
        try
          let new_lvi = Logic_var.Hashtbl.find already_visited orig_lvi in
          (* recreate sharing of the logic_var in this [spec] *)
          Cil.ChangeTo new_lvi
        with Not_found ->
          (* first time visiting this logic var *)
          Cil.ChangeDoChildrenPost
            ({ orig_lvi with lv_id = orig_lvi.lv_id } (* force a copy *),
             fun lvi ->
               try
                 let new_vi = Varinfo.Hashtbl.find formals vi in
                 Logic_var.Hashtbl.add already_visited orig_lvi lvi;
                 (* [lvi] is the logic counterpart of a formal varinfo that has
                    been replaced by a new one: propagate this change *)
                 lvi.lv_id <- new_vi.vid;
                 lvi.lv_name <- new_vi.vname;
                 lvi.lv_origin <- Some new_vi;
                 new_vi.vlogic_var_assoc <- Some lvi;
                 lvi
               with Not_found ->
                 assert vi.vglob;
                 lvi)

  end in
  Cil.visitCilFunspec (o :> Cil.cilVisitor) spec

let dup_fundec loc spec sound_verdict_vi kf vi new_vi =
  new_vi.vdefined <- true;
  let formals = Kernel_function.get_formals kf in
  let mk_formal vi =
    let name =
      if vi.vname = "" then
        (* unnamed formal parameter: must generate a fresh name since a fundec
           cannot have unnamed formals (see bts #2303). *)
        Varname.get
          ~scope:Varname.Function
          (Functions.RTL.mk_gen_name "unamed_formal")
      else
        vi.vname
    in
    Cil.copyVarinfo vi name
  in
  let new_formals = List.map mk_formal formals in
  let res =
    let ty = Kernel_function.get_return_type kf in
    if Cil.isVoidType ty
    then None
    else Some (Cil.makeVarinfo false false ~referenced:true "__retres" ty)
  in
  let return =
    Cil.mkStmt ~valid_sid:true
      (Return(Option.map (Cil.evar ~loc) res, loc))
  in
  let stmts =
    let l =
      [ Cil.mkStmtOneInstr ~valid_sid:true
          (Call(Option.map Cil.var res,
                Cil.evar ~loc vi,
                List.map (Cil.evar ~loc) new_formals,
                loc));
        return ]
    in
    if Functions.instrument kf then
      l
    else
      (* set the 'sound_verdict' variable to 'false' whenever required *)
      let unsound =
        Cil.mkStmtOneInstr ~valid_sid:true
          (Set((Var sound_verdict_vi, NoOffset), Cil.zero ~loc, loc))
      in
      unsound :: l
  in
  let locals = match res with None -> [] | Some r -> [ r ] in
  let body = Cil.mkBlock stmts in
  body.blocals <- locals;
  let tbl = Varinfo.Hashtbl.create 7 in
  List.iter2 (Varinfo.Hashtbl.add tbl) formals new_formals;
  let new_spec = dup_funspec tbl spec in
  let fundec =
    { svar = new_vi;
      sformals = new_formals;
      slocals = locals;
      smaxid = List.length new_formals;
      sbody = body;
      smaxstmtid = None;
      sallstmts = [];
      sspec = new_spec }
  in
  (* compute the CFG of the new [fundec] *)
  Cfg.clearCFGinfo ~clear_id:false fundec;
  Cfg.cfgFun fundec;
  fundec

let dup_global loc spec sound_verdict_vi kf vi new_vi =
  let name = vi.vname in
  Options.feedback ~dkey ~level:2 "entering in function %s" name;
  let new_fundec = dup_fundec loc spec sound_verdict_vi kf vi new_vi  in
  let new_fct = Definition(new_fundec, loc) in
  let new_spec = new_fundec.sspec in
  let new_kf = { fundec = new_fct; spec = new_spec } in
  Globals.Functions.register new_kf;
  Globals.Functions.replace_by_definition new_spec new_fundec loc;
  Annotations.register_funspec new_kf;
  if Datatype.String.equal new_vi.vname "main" then begin
    (* recompute kernel's info about the old main since its name has changed;
       see the corresponding part in the main visitor *)
    Globals.Functions.remove vi;
    Globals.Functions.register kf
  end;
  (* copy property statuses to the new spec *)
  let copy old_ip new_ip =
    let open Property_status in
    let cp status ep =
      let e = Emitter.Usable_emitter.get ep.emitter in
      if ep.logical_consequence
      then logical_consequence e new_ip ep.properties
      else
        let status, hyps =
          match status, ep.properties with
          | True, _ | Dont_know, _
          | False_and_reachable, [] | False_if_reachable, [] ->
            (* Valid emission: either [true] status with arbitrary hypotheses or
               [false] status with empty hypotheses. *)
            status, ep.properties
          | False_and_reachable, [ IPReachable _ ]
          | False_if_reachable, [ IPReachable _ ] ->
            (* [False] status with a reachability hypothesis: remove the
               hypothesis and set the status to [False_if_reachable]. *)
            False_if_reachable, []
          | False_and_reachable, hyps | False_if_reachable, hyps ->
            (* Invalid emission: [false] status with arbitrary hypotheses. *)
            Options.fatal
              "Property with status '%s' and non-empty hypotheses:\n\
               * Property: %a\n\
               * Hypotheses:\n- %a"
              (match status with
               | True -> "True"
               | Dont_know -> "Dont_know"
               | False_if_reachable -> "False_if_reachable"
               | False_and_reachable -> "False_and_reachable")
              Property.short_pretty new_ip
              (Pretty_utils.pp_list ~sep:"\n- " Property.short_pretty) hyps
        in
        emit e new_ip ~hyps status
    in
    match get old_ip with
    | Never_tried ->
      ()
    | Best(s, epl) ->
      List.iter (cp s) epl
    | Inconsistent icst ->
      List.iter (cp True) icst.valid;
      (* Copy invalid properties with [False_and_reachable], if a reachability
         hypothesis is present then the [cp] function will convert it to
         [False_if_reachable]. *)
      List.iter (cp False_and_reachable) icst.invalid
  in
  let ips kf s = Property.ip_of_spec kf Kglobal ~active:[] s in
  List.iter2 copy (ips kf spec) (ips new_kf new_spec);
  (* remove annotations from the old spec. Yet keep them in functions only
     declared since, otherwise, the kernel would complain about functions
     with neither contract nor body  *)
  if Kernel_function.is_definition kf then begin
    let old_bhvs =
      Annotations.fold_behaviors (fun e b acc -> (e, b) :: acc) kf []
    in
    List.iter
      (fun (e, b) -> Annotations.remove_behavior ~force:true e kf b)
      old_bhvs;
    Annotations.iter_decreases
      (fun e _ -> Annotations.remove_decreases e kf)
      kf;
    Annotations.iter_terminates
      (fun e _ -> Annotations.remove_terminates e kf)
      kf;
    Annotations.iter_complete
      (fun e l -> Annotations.remove_complete e kf l)
      kf;
    Annotations.iter_disjoint
      (fun e l -> Annotations.remove_disjoint e kf l)
      kf
  end;
  GFun(new_fundec, loc), GFunDecl(new_spec, new_vi, loc)

(* ********************************************************************** *)
(* Alignment *)
(* ********************************************************************** *)

(* Returns true if the list of attributes [attrs] contains an [align] attribute
   of [algn] or greater. Returns false otherwise.
   Throws an exception if
   - [attrs] contains several [align] attributes specifying different
     alignments
   - [attrs] has a single align attribute with a value which is less than
     [algn] *)
let sufficiently_aligned vi algn =
  let alignment =
    List.fold_left
      (fun acc attr ->
         match attr with
         | Attr("align", [AInt i]) ->
           let alignment = Integer.to_int_exn i in
           if acc <> 0 && acc <> alignment then begin
             (* multiple align attributes with different values *)
             Options.error
               "multiple alignment attributes with different values for\
                variable %a. Keeping the last one."
               Printer.pp_varinfo vi;
             alignment
           end else if alignment < algn then begin
             (* if there is an alignment attribute it should be greater or equal
                to [algn] *)
             Options.error
               "alignment of variable %a should be greater or equal to %d.@ \
                Continuing with this value."
               Printer.pp_varinfo vi
               algn;
             algn
           end else
             alignment
         | Attr("align", _) ->
           (* align attribute with an argument other than a single number,
              should not happen really *)
           assert false
         | _ -> acc)
      0
      vi.vattr
  in
  alignment > 0

(* return [true] iff the given [vi] requires to be aligned at the boundary
   of [algn] (i.e., less than [algn] bytes and has no alignment attribute) *)
let require_alignment vi algn =
  Cil.bitsSizeOf vi.vtype < algn*8 && not (sufficiently_aligned vi algn)

(* ********************************************************************** *)
(* Visiting the globals *)
(* ********************************************************************** *)

(** Module for ensuring absence of term sharing *)
module Term_sharing: sig
  val add: term -> unit
  val mem: term -> bool
  val clear: unit -> unit
end
=
struct
  let terms = Misc.Id_term.Hashtbl.create 7
  let add t = Misc.Id_term.Hashtbl.add terms t ()
  let mem t = Misc.Id_term.Hashtbl.mem terms t
  let clear () = Misc.Id_term.Hashtbl.clear terms
end

(** Module to move labels to an enclosing block *)
module Labeled_stmts: sig
  (* [add_moved_stmt old new] records that the labels have been moved from
     statement [old] to statement [new]. *)
  val add_moved_stmt: stmt -> stmt -> unit

  (* [add_stmt_ref s_ref] adds the reference [s_ref] to the list of references
     to update to the moved labeled statement. *)
  val add_stmt_ref: stmt ref -> unit

  (* [add_stmt s] adds the statement [s] to the list of statements to update
     so that inner statement fields are updated to the moved labeled
     statements. *)
  val add_stmt: stmt -> unit

  (* [set_fundec_has_label ()] sets the boolean indicating that the current
     [fundec] has some labeled statements. *)
  val set_fundec_has_label: unit -> unit

  (* [clear ()] clears the internal fields of the module. *)
  val clear: unit -> unit

  (* [get_moved_stmt old], if [old] was a labeled statement, returns the new
     statement where the labels have been moved, otherwise returns [old]. *)
  val get_moved_stmt: stmt -> stmt

  (* [update_in_fundec fundec] updates the function [fundec] with the updated
     labeled statements. *)
  val update_in_fundec: fundec -> unit
end
=
struct
  (* Hold the association between the original statement with labels and the
     statement where the labels have been moved. *)
  let moved_labels: stmt Stmt.Hashtbl.t = Stmt.Hashtbl.create 17

  (* List of [ref stmt] that need to be updated if they point to a labeled
     statement. *)
  let stmt_refs: stmt ref list ref = ref []

  (* List of [stmt] containing other statements that need to be udpated if
     they point to a labeled statement. *)
  let stmts: stmt list ref = ref []

  (* True if the current [fundec] had a label, false otherwise. *)
  let fundec_has_label: bool ref = ref false

  let clear () =
    Stmt.Hashtbl.clear moved_labels;
    stmt_refs := [];
    stmts := [];
    fundec_has_label := false

  let add_moved_stmt stmt new_stmt =
    Stmt.Hashtbl.add moved_labels stmt new_stmt
  let add_stmt_ref s_ref = stmt_refs := s_ref :: !stmt_refs
  let add_stmt s = stmts := s :: !stmts
  let set_fundec_has_label () = fundec_has_label := true

  (* If the given statement had labels that have been moved, return the new
     labeled statement, otherwise return the given statement. *)
  let get_moved_stmt stmt =
    try Stmt.Hashtbl.find moved_labels stmt
    with Not_found -> stmt

  (* Visitor to update statements that contain labeled statements such as
     [switch] or [loop]. *)
  let stmt_updater =
    object
      inherit Visitor.frama_c_inplace

      method !vstmt_aux stmt =
        match stmt.skind with
        | Switch (e, b, slist, loc) ->
          let slist = List.map get_moved_stmt slist in
          stmt.skind <- Switch (e, b, slist, loc);
          Cil.ChangeTo stmt
        | Loop (ca, b, loc, cont_stmt_opt, brk_stmt_opt) ->
          let continue_stmt_opt =
            Option.map get_moved_stmt cont_stmt_opt
          in
          let break_stmt_opt = Option.map get_moved_stmt brk_stmt_opt in
          stmt.skind <- Loop (ca, b, loc, continue_stmt_opt, break_stmt_opt);
          Cil.ChangeTo stmt
        | _ -> Cil.SkipChildren
    end

  let update_in_fundec fundec =
    (* Update all [ref stmt] retrieved with the visitor. *)
    List.iter
      (fun s_ref -> s_ref := get_moved_stmt !s_ref)
      !stmt_refs;
    (* Update all [stmt] retrieved with the visitor. *)
    List.iter
      (fun s ->
         ignore @@ Visitor.visitFramacStmt stmt_updater s)
      !stmts;
    (* If a label was found in the function, update the CFG. *)
    if !fundec_has_label then begin
      Cfg.clearCFGinfo ~clear_id:false fundec;
      Cfg.cfgFun fundec;
    end

end

(* perform a few modifications in the [kf]'s code and annotations that are
   required by E-ACSL's analyses and transformations *)
let prepare_fundec kf =
  let o = object
    inherit Visitor.frama_c_inplace

    (* substitute function's varinfos by their duplicate in function calls *)
    method !vvrbl vi =
      try Cil.ChangeTo (Dup_functions.find vi)
      with Not_found -> Cil.SkipChildren

    (* temporal analysis requires that attributes are aligned to local
       variables *)
    method !vblock _ =
      if Options.Temporal_validity.get () then
        Cil.DoChildrenPost
          (fun blk ->
             List.iter
               (fun vi ->
                  (* 4 bytes alignment is required to allow sufficient space for
                     storage of 32-bit timestamps in a 1:1 shadow. *)
                  if require_alignment vi 4 then
                    vi.vattr <-
                      Attr("aligned", [ AInt Integer.four ]) :: vi.vattr)
               blk.blocals;
             blk)
      else
        Cil.DoChildren

    (* remove term sharing introduced by the Frama-C kernel. For instance, an
       annotation such as [a <= t <= b] is replaced by [a <= t && t <= b] with
       both occurrences of [t] being shared. Yet, the E-ACSL type system may
       require to assign them different types. *)
    method !vterm _ =
      Cil.DoChildrenPost
        (fun t ->
           if Term_sharing.mem t then
             { t with term_node = t.term_node }
           else begin
             Term_sharing.add t;
             t
           end)

    method !videntified_predicate _ =
      (* when entering a new annotation, clear the context to keep it small:
         anyway, no sharing is possible between two identified predicates *)
      Term_sharing.clear ();
      Cil.DoChildren

    method !vfunc _ =
      Labeled_stmts.clear ();
      Cil.DoChildrenPost
        (fun fundec ->
           Labeled_stmts.update_in_fundec fundec;
           fundec)

    method !vstmt_aux _ =
      Cil.DoChildrenPost
        (fun stmt ->
           (* Save the [ref stmt] and [stmt] contained in the current stmt to
              update them at the end of the function visit. *)
           begin
             match stmt.skind with
             | Goto(s_ref, _) ->
               Labeled_stmts.add_stmt_ref s_ref
             | Switch _ | Loop _ ->
               Labeled_stmts.add_stmt stmt
             | UnspecifiedSequence seq ->
               List.iter
                 (fun (_, _, _, _, s_ref_list) ->
                    List.iter
                      Labeled_stmts.add_stmt_ref
                      s_ref_list)
                 seq
             | Instr (Asm (_, _, extasm_opt, _)) ->
               Option.iter
                 (function { asm_gotos } ->
                    List.iter
                      Labeled_stmts.add_stmt_ref
                      asm_gotos)
                 extasm_opt
             | _ -> ()
           end;
           (* If the current statement has labels, create an enclosing block and
              move the labels to it. *)
           match stmt.labels with
           | [] -> stmt
           | _ :: _ ->
             let labels = stmt.labels in
             let new_stmt =
               Cil.mkStmt ~valid_sid:true (Block (Cil.mkBlock [ stmt ]))
             in
             stmt.labels <- [];
             new_stmt.labels <- labels;
             Labeled_stmts.set_fundec_has_label ();
             Labeled_stmts.add_moved_stmt stmt new_stmt;
             new_stmt)

    method !vlogic_label ll =
      (* Since the logic labels can only reference previous labels, we can
         update the [ref stmt] of [StmtLabel] directly here. *)
      begin
        match ll with
        | StmtLabel s_ref ->
          s_ref := Labeled_stmts.get_moved_stmt !s_ref;
        | BuiltinLabel _ | FormalLabel _ -> ()
      end;
      Cil.DoChildren

  end in
  ignore (Visitor.visitFramacKf o kf)

(* the variable [sound_verdict] belongs to the E-ACSL's RTL and indicates
   whether the verdict emitted by E-ACSL is sound. It needs to be visible at
   that point because it is set in all function duplicates (see
   [dup_fundec]). *)
let sound_verdict_vi =
  lazy
    (let name = Functions.RTL.mk_api_name "sound_verdict" in
     let vi = Cil.makeGlobalVar name Cil.intType in
     vi.vstorage <- Extern;
     vi.vreferenced <- true;
     vi.vattr <- Cil.addAttribute (Attr ("FC_BUILTIN", [])) vi.vattr;
     vi)

let sound_verdict () = Lazy.force sound_verdict_vi

let is_variadic_function vi = match Cil.unrollType vi.vtype with
  | TFun(_, _, variadic, _) -> variadic
  | _ -> false

(* set of functions that must never be duplicated *)
let unduplicable_functions =
  let white_list =
    [ "__builtin_va_arg";
      "__builtin_va_end";
      "__builtin_va_start";
      "__builtin_va_copy";
      (* *alloc and free should not be duplicated. *)
      (* [TODO:] it preserves the former behavior. Should be modified latter by
         checking only preconditions for any libc functions, see e-acsl#35 *)
      "malloc";
      "calloc";
      "realloc";
      "free" ]
  in
  List.fold_left
    (fun acc s -> Datatype.String.Set.add s acc)
    Datatype.String.Set.empty
    white_list

let must_duplicate kf vi =
  (* it is not already duplicated *)
  not (Dup_functions.mem vi)
  && (* it is duplicable *)
  not (Datatype.String.Set.mem vi.vname unduplicable_functions)
  && (* it is not a variadic function *)
  not (is_variadic_function vi)
  && (* it is not a built-in *)
  not (Misc.is_fc_or_compiler_builtin vi)
  && (* it is not a generated function *)
  not (Misc.is_fc_stdlib_generated vi)
  &&
  ((* either explicitely listed as to be not instrumented *)
    not (Functions.instrument kf)
    ||
    (* or: *)
    ((* it has a function contract *)
      not (Cil.is_empty_funspec (Annotations.funspec ~populate:false kf))
      && (* its annotations must be monitored *)
      Functions.check kf))

let prepare_global (globals, new_defs) = function
  | GFunDecl(_, vi, loc) | GFun({ svar = vi }, loc) as g ->
    let kf = try Globals.Functions.get vi with Not_found -> assert false in
    if must_duplicate kf vi then begin
      let new_vi = Dup_functions.generate_vi vi in
      if Kernel_function.is_definition kf then
        prepare_fundec kf
      else if not (!is_libc_writing_memory_ref vi) then
        (* Only display the warning for functions where E-ACSL does not
           explicitely update its memory model. *)
        (* TODO: this warning could be more precise if emitted during code
           generation; see also E-ACSL issue #85 about partial verdicts *)
        Options.warning
          "@[annotating undefined function `%a':@ \
           the generated program may miss memory instrumentation@ \
           if there are memory-related annotations.@]"
          Printer.pp_varinfo vi;
      let tmp = vi.vname in
      if Datatype.String.equal tmp "main" then begin
        (* the new function becomes the new main: *)
        (* 1. swap the name of both functions *)
        vi.vname <- new_vi.vname;
        new_vi.vname <- tmp;
        (* 2. force recomputation of the entry point if necessary *)
        if Kernel.MainFunction.get () = tmp then begin
          let selection =
            State_selection.with_dependencies Kernel.MainFunction.self
          in
          Project.clear ~selection ()
        end
      end;
      let new_def, new_decl =
        dup_global
          loc
          (Annotations.funspec ~populate:false kf)
          (Lazy.force sound_verdict_vi)
          kf
          vi
          new_vi
      in
      (* postpone the introduction of the new function definition *)
      let new_defs = new_def :: new_defs in
      (* put the declaration before the original function in order to solve
         issues with recursive functions *)
      g :: new_decl :: globals, new_defs
    end else begin (* not duplicated *)
      prepare_fundec kf;
      g :: globals, new_defs
    end
  | g ->
    (* nothing to do for globals that are not functions *)
    g :: globals, new_defs

let prepare_file file =
  Dup_functions.reset ();
  let rev_globals, new_defs =
    List.fold_left prepare_global ([], []) file.globals
  in
  (* insert the new_definitions at the end and reverse back the globals *)
  let globals = List.fold_left (fun acc g -> g :: acc) new_defs rev_globals in
  (* insert [__e_acsl_sound_verdict] at the beginning *)
  let sg = GVarDecl(Lazy.force sound_verdict_vi, Location.unknown) in
  file.globals <- sg :: globals

let prepare () =
  Options.feedback ~level:2 "prepare AST for E-ACSL transformations";
  prepare_file (Ast.get ());
  Ast.mark_as_grown ()

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
