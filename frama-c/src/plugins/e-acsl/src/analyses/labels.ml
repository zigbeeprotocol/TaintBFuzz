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

(** Pre-analysis for Labeled terms and predicates. *)

open Cil_types
open Cil_datatype
open Analyses_types
open Analyses_datatype
let dkey = Options.Dkey.labels
module Error = Error.Make(struct let phase = dkey end)

(**************************************************************************)
(********************** Forward references ********************************)
(**************************************************************************)

let has_empty_quantif_ref: ((term * logic_var * term) list -> bool) ref =
  Extlib.mk_fun "has_empty_quantif_ref"

(**************************************************************************)
(************************** Labeled stmts *********************************)
(**************************************************************************)

let get_first_inner_stmt stmt =
  match stmt.labels, stmt.skind with
  | [], _ -> stmt
  | _ :: _, Block { bstmts = dest_stmt :: _ } ->
    dest_stmt
  | labels, _ ->
    Options.fatal "Unexpected stmt:\nlabels: [%a]\nstmt: %a"
      (Pretty_utils.pp_list ~sep:"; " Cil_types_debug.pp_label) labels
      Printer.pp_stmt stmt

(**************************************************************************)
(*************************** Translation **********************************)
(**************************************************************************)

let preprocess_done = ref false

(** Associate a statement with the [at_data] that need to be translated on
    this statement. *)
let at_data_for_stmts: At_data.Set.t ref Stmt.Hashtbl.t =
  Stmt.Hashtbl.create 17

(** Add [data] to the list of [at_data] that must be translated on the
    statement [stmt]. *)
let add_at_for_stmt data stmt =
  let stmt = get_first_inner_stmt stmt in
  let ats_ref =
    try
      Stmt.Hashtbl.find at_data_for_stmts stmt
    with Not_found ->
      let ats_ref = ref At_data.Set.empty in
      Stmt.Hashtbl.add at_data_for_stmts stmt ats_ref;
      ats_ref
  in
  let old_data =
    try
      At_data.Set.find data !ats_ref
    with Not_found ->
      ats_ref := At_data.Set.add data !ats_ref;
      data
  in
  match old_data.error, data.error with
  | Some _, None ->
    (* Replace the old data that has an error with the new data that do not
       have one. *)
    ats_ref := At_data.Set.remove old_data !ats_ref;
    ats_ref := At_data.Set.add data !ats_ref
  | Some _, Some _
  | None, Some _
  | None, None ->
    (* Either the new data has an error and not the old one, or both data are
       the same, keep the old data. *)
    ()

(* see documentation in .mli *)
let at_for_stmt stmt =
  if !preprocess_done then
    let ats_ref =
      Stmt.Hashtbl.find_def at_data_for_stmts stmt (ref At_data.Set.empty)
    in
    Result.Ok !ats_ref
  else
    Error.not_memoized ()

(**************************************************************************)
(************************** AST traversal *********************************)
(**************************************************************************)

module Process: sig
  module Env: sig
    type t
    (** Environment to propagate during the traversal. *)

    val create:
      kernel_function ->
      kinstr ->
      annotation_kind ->
      t
      (** [create clabels kf kinstr akind] creates an environment for the
          traversal.
          - [kf]: Enclosing function of the predicate or term being analysed.
          - [kinstr]: Kinstr of the predicate or term being analysed.
          - [akind]: Kind of annotation for the predicate or term being
            analysed. *)
  end

  val term: ?error:exn -> Env.t -> term -> unit
  (** Traverse the given term to analyze its labeled predicates and terms. *)

  val predicate: ?error:exn -> Env.t -> predicate -> unit
  (** Traverse the given predicate to analyze its labeled predicates and
      terms. *)

end = struct
  module Env = struct
    type t = {
      kf: kernel_function;
      (** Enclosing function of the predicate or term being analysed. *)
      kinstr: kinstr;
      (** Kinstr of the predicate or term being analysed. *)
      akind: annotation_kind;
      (** Kind of annotation for the predicate or term being analysed. *)
      lscope: Lscope.t;
      (** Logic scope for the predicate or term being analysed. *)
    }

    let create kf kinstr akind =
      { kf; kinstr; akind; lscope = Lscope.empty }
  end

  (** @return either the given error if it is provided, or [Some e] if not. *)
  let set_error ?error e =
    match error with
    | None -> Some e
    | Some _ -> error

  (** Create and return a [Not_yet] exception with the given message. If [error]
      is provided, return this error instead. *)
  let not_yet ?error s =
    set_error ?error (Error.make_not_yet s)

  (** Apply [fct ?error env] on every element of the list [args]. *)
  let do_list fct ?error env args =
    List.fold_left
      (fun error a -> fct ?error env a)
      error
      args

  (** Apply [fct ?error env] on [arg] if [arg_opt] is [Some arg], return
      directly [error] otherwise. *)
  let do_opt fct ?error env arg_opt =
    match arg_opt with
    | Some arg -> fct ?error env arg
    | None -> error

  (** Analyse the predicate or term [pot] and the label [label] to decide where
      the predicate or term must be translated. *)
  let process ?error env pot label =
    Env.( (* locally open Env to access to the fields of Env.t *)
      let msg s =
        Format.asprintf
          "%s '%a' within %s annotation '%a' in '%a'"
          s
          Printer.pp_logic_label label
          (match env.kinstr with
           | Kglobal -> "function"
           | Kstmt _ -> "statement")
          Annotation_kind.pretty env.akind
          Pred_or_term.pretty pot
      in
      let error, dest_stmt_opt =
        match env.kinstr, env.akind, label with
        (* C label, translate on the given statement regardless of the kind of
           annotation. *)
        | Kstmt _, _, StmtLabel { contents = stmt } ->
          error, Some stmt
        | Kglobal, _, StmtLabel _ ->
          Options.fatal "%s" (msg "invalid use of C label")

        (* Assertions *)
        (* - Pre label corresponding to the first statement of the function *)
        | Kstmt _, Assertion, BuiltinLabel Pre ->
          error, Some (Kernel_function.find_first_stmt env.kf)
        (* - In-place translation for label Here *)
        | Kstmt _, Assertion, BuiltinLabel Here ->
          error, None
        (* - Not yet supported labels *)
        | Kstmt _, Assertion, BuiltinLabel (LoopCurrent | LoopEntry | Init) ->
          not_yet ?error (msg "label"), None
        (* - Invalid labels in assertions *)
        | Kstmt _, Assertion, BuiltinLabel (Old | Post) ->
          Options.fatal "%s" (msg "invalid label")
        (* - Invalid use of assertion in function contract *)
        | Kglobal, Assertion, _ ->
          Options.fatal "invalid use of assertion in fonction contract"

        (* Function contracts *)
        (* - Preconditions *)
        (* -- In-place translation for labels Pre, Old and Here *)
        | Kglobal, Precondition, BuiltinLabel (Pre | Old | Here) ->
          error, None
        (* -- Not yet supported labels *)
        | Kglobal, Precondition, BuiltinLabel Init ->
          not_yet ?error (msg "label"), None
        (* -- Invalid labels *)
        | Kglobal, Precondition, BuiltinLabel (Post | LoopEntry | LoopCurrent)
          ->
          Options.fatal "%s" (msg "invalid label")
        (* - Postconditions *)
        (* -- Pre and Old are equivalent and correspond to the first statement
           of the function. *)
        | Kglobal, Postcondition, BuiltinLabel (Pre | Old) ->
          error, Some (Kernel_function.find_first_stmt env.kf)
        (* -- In-place translation for labels Here and Post *)
        | Kglobal, Postcondition, BuiltinLabel (Here | Post) ->
          error, None
        (* -- Not yet supported labels *)
        | Kglobal, Postcondition, BuiltinLabel Init ->
          not_yet ?error (msg "label"), None
        (* -- Invalid labels *)
        | Kglobal, Postcondition, BuiltinLabel (LoopEntry | LoopCurrent) ->
          Options.fatal "%s" (msg "invalid label")
        (* - Variant *)
        | Kglobal, Variant, _ ->
          Options.fatal "invalid use of label in decreases clause"
        (* - Invariant *)
        | Kglobal, Invariant, _ ->
          Options.fatal "invalid invariant annotation in function contract"

        (* Statement contracts *)
        (* - Preconditions *)
        (* -- Pre correspond to the first statement of the function *)
        | Kstmt _, Precondition, BuiltinLabel Pre ->
          error, Some (Kernel_function.find_first_stmt env.kf)
        (* -- In-place translation for Old and Here *)
        | Kstmt _, Precondition, BuiltinLabel (Old | Here) ->
          error, None
        (* -- Not yet supported labels *)
        | Kstmt _, Precondition, BuiltinLabel (Init | LoopEntry | LoopCurrent)
          ->
          not_yet ?error (msg "label"), None
        (* -- Invalid labels *)
        | Kstmt _, Precondition, BuiltinLabel Post ->
          Options.fatal "%s" (msg "invalid label")
        (* - Postconditions *)
        (* -- Pre correspond to the first statement of the function *)
        | Kstmt _, Postcondition, BuiltinLabel Pre ->
          error, Some (Kernel_function.find_first_stmt env.kf)
        (* -- Old correspond to the current statement *)
        | Kstmt stmt, Postcondition, BuiltinLabel Old ->
          error, Some stmt
        (* -- In-place tranlsation for Here and Post *)
        | Kstmt _, Postcondition, BuiltinLabel (Here | Post) ->
          error, None
        (* -- Not yet supported labels *)
        | Kstmt _, Postcondition, BuiltinLabel (Init | LoopEntry | LoopCurrent)
          ->
          not_yet ?error (msg "label"), None
        (* - Variant *)
        | Kstmt _, Variant, _ ->
          not_yet ?error "label in loop variant", None
        (* - Invariant *)
        | Kstmt _, Invariant, _ ->
          not_yet ?error "label in loop invariant", None

        (* Global annotation labels are not supported in E-ACSL *)
        | _, _, FormalLabel _ ->
          not_yet ?error (msg "formal label"), None

        | _, RTE, _ ->
          Options.fatal "%s" (msg "invalid annotation kind in")
      in
      begin match dest_stmt_opt with
        | Some dest_stmt ->
          (* Register the current labeled pred_or_term to the destination
             statement for a later translation *)
          let at =
            At_data.create ?error env.kf env.kinstr env.lscope pot label
          in
          add_at_for_stmt at dest_stmt;
        | None ->
          ()
      end;
      error
    )

  (** Term traversal *)
  let rec do_term ?error env t =
    let t = Logic_normalizer.get_term t in
    match t.term_node with
    | Tat (t', l) ->
      let error = do_term ?error env t' in
      process ?error env (PoT_term t) l
    | Tbase_addr (l, t') | Tblock_length (l, t') | Toffset (l, t') ->
      let error = do_term ?error env t' in
      (* E-ACSL semantic: \base_addr{L}(p) == \at(\base_addr(p), L) *)
      process ?error env (PoT_term t) l
    | Tlet (li, t) ->
      let lv_term = Misc.term_of_li li in
      let error = do_term ?error env lv_term in
      let lvs = Lvs_let (li.l_var_info, lv_term) in
      let env = { env with lscope = Lscope.add lvs env.lscope } in
      do_term ?error env t
    | TLval lv | TAddrOf lv | TStartOf lv ->
      do_term_lval ?error env lv
    | TSizeOfE t | TAlignOfE t | TUnOp (_, t) | TCastE (_, t) | Tlambda (_, t)
    | TLogic_coerce (_, t) ->
      do_term ?error env t
    | TBinOp (_, t1, t2) ->
      let error = do_term ?error env t1 in
      do_term ?error env t2
    | Tif (t1, t2, t3) ->
      let error = do_term ?error env t1 in
      let error = do_term ?error env t2 in
      do_term ?error env t3
    | Tapp (_, [], targs) ->
      do_list do_term ?error env targs
    | Tapp (_, labels, targs) ->
      let error = not_yet "logic functions with labels" in
      do_labeled_app ?error env labels targs
    | Trange (t1_opt, t2_opt) ->
      let error = do_opt do_term ?error env t1_opt in
      do_opt do_term ?error env t2_opt
    | TDataCons (_, targs) ->
      (* Register a not_yet error for each labeled pred or term in the
         arguments *)
      let error = not_yet "constructor" in
      do_list do_term ?error env targs
    | TUpdate (t1, toff, t2) ->
      (* Register a not_yet error for each labeled pred or term used in the
         functional update *)
      let error = not_yet "functional update" in
      let error = do_term ?error env t1 in
      let error = do_term_offset ?error env toff in
      do_term ?error env t2
    | Ttypeof t ->
      (* Register a not_yet error for each labeled pred or term used with the
         typeof operator *)
      let error = not_yet "typeof" in
      do_term ?error env t
    | Tunion ts | Tinter ts ->
      (* Register a not_yet error for each labeled pred or term used in the
         manipulation of tsets *)
      let error = not_yet "union or intersection of tsets" in
      do_list do_term ?error env ts
    | Tcomprehension (t, _, p_opt) ->
      (* Register a not_yet error for each labeled pred or term used in the
         comprehension *)
      let error = not_yet "tset comprehension" in
      let error = do_term ?error env t in
      do_opt do_predicate ?error env p_opt
    | TConst _ | TSizeOf _ | TAlignOf _ | TSizeOfStr _ | Tnull | Ttype _
    | Tempty_set ->
      error

  (** Lval traversal *)
  and do_term_lval ?error env (tlhost, toffset) =
    let error = do_term_lhost ?error env tlhost in
    do_term_offset ?error env toffset

  (** Lhost traversal *)
  and do_term_lhost ?error env = function
    | TMem t -> do_term ?error env t
    | TVar _ | TResult _ -> error

  (** Offset traversal *)
  and do_term_offset ?error env = function
    | TIndex (t, next) ->
      let error = do_term ?error env t in
      do_term_offset ?error env next
    | TField (_, next) | TModel (_, next) ->
      do_term_offset ?error env next
    | TNoOffset -> error

  (** Predicate traversal *)
  and do_predicate ?error env p =
    let p = Logic_normalizer.get_pred p in
    match p.pred_content with
    | Pat (p', l) ->
      let error = do_predicate ?error env p' in
      process ?error env (PoT_pred p) l
    | Pfreeable (l, t) | Pvalid (l, t) | Pvalid_read (l, t)
    | Pinitialized (l, t)  ->
      let error = do_term ?error env t in
      (* E-ACSL semantic: \freeable{L}(p) == \at(\freeable(p), L) *)
      process ?error env (PoT_pred p) l
    | Pallocable (l, t) ->
      let error = not_yet "\\allocate" in
      let error = do_term ?error env t in
      process ?error env (PoT_pred p) l
    | Pdangling (l, t) ->
      let error = not_yet "\\dangling" in
      let error = do_term ?error env t in
      process ?error env (PoT_pred p) l
    | Pobject_pointer (l, t) ->
      let error = not_yet "\\object_pointer" in
      let error = do_term ?error env t in
      process ?error env (PoT_pred p) l
    | Plet (li, p) ->
      let lv_term = Misc.term_of_li li in
      let error = do_term ?error env lv_term in
      let lvs = Lvs_let (li.l_var_info, lv_term) in
      let env = { env with lscope = Lscope.add lvs env.lscope } in
      do_predicate ?error env p
    | Pforall _ | Pexists _ -> begin
        let preprocessed_quantifier_or_error =
          try
            Bound_variables.get_preprocessed_quantifier p
          with Error.Not_memoized _ ->
            Options.fatal
              "preprocessing of quantifier '%a' has not been performed"
              Printer.pp_predicate p
        in
        match preprocessed_quantifier_or_error with
        | Result.Ok (bound_vars, goal) ->
          if !has_empty_quantif_ref bound_vars then
            error
          else begin
            (* We want to process the bounds and the predicate with the same
               environment as the translation (done in [Quantif.convert]). As a
               result, the [lscope] is first built with a [fold_right] on the
               [bound_vars], then once the [lscope] is entirely built, the terms
               of the bounds and the predicate of the goal are analyzed. *)
            let env =
              List.fold_right
                (fun (t1, lv, t2) env ->
                   let lvs = Lvs_quantif (t1, Rle, lv, Rlt, t2) in
                   { env with Env.lscope = Lscope.add lvs env.Env.lscope })
                bound_vars
                env
            in
            let do_it ?error env (t1, _, t2) =
              let error = do_term ?error env t1 in
              do_term ?error env t2
            in
            let error = do_list do_it ?error env bound_vars in
            do_predicate ?error env goal
          end
        | Result.Error exn -> set_error ?error exn
      end
    | Pnot p ->
      do_predicate ?error env p
    | Pand (p1, p2) | Por (p1, p2) | Pxor (p1, p2) | Pimplies (p1, p2)
    | Piff (p1, p2) ->
      let error = do_predicate ?error env p1 in
      do_predicate ?error env p2
    | Pif (t, p1, p2) ->
      let error = do_term ?error env t in
      let error = do_predicate ?error env p1 in
      do_predicate ?error env p2
    | Prel (_, t1, t2) ->
      let error = do_term ?error env t1 in
      do_term ?error env t2
    | Papp (_, [], targs) | Pseparated (targs) ->
      do_list do_term ?error env targs
    | Papp (_, labels, targs) ->
      let error = not_yet "predicate with labels" in
      do_labeled_app ?error env labels targs
    | Pvalid_function t ->
      let error = not_yet "\\valid_function" in
      do_term ?error env t
    | Pfresh (l1, l2, t, _) ->
      let error = not_yet "\\fresh" in
      let error = process ?error env (PoT_term t) l1 in
      process ?error env (PoT_term t) l2
    | Pfalse | Ptrue -> error

  (** Function application with labels traversal *)
  and do_labeled_app ?error env labels targs =
    let do_it ?error env t =
      (* Register a not_yet error for each labeled pred or term in the
         arguments *)
      let error = do_term ?error env t in
      (* Since we do not know how the labels are used with the arguments,
         for each argument, register a [Not_yet] error with each label of the
         function so that each possible combination gracefully raises an error
         to the user. *)
      List.fold_left
        (fun error label -> process ?error env (PoT_term t) label)
        error
        labels
    in
    do_list do_it ?error env targs

  (* see documentation in module signature *)
  let term ?error env t =
    ignore @@ do_term ?error env t

  (* see documentation in module signature *)
  let predicate ?error env p =
    ignore @@ do_predicate ?error env p

end

class vis_at_labels () = object (self)

  inherit E_acsl_visitor.visitor dkey

  method! glob_annot _ = Cil.SkipChildren

  (** Launch the analysis on the given predicate. *)
  method! vpredicate p =
    let kf = Option.get self#current_kf in
    let kinstr = self#current_kinstr in
    let akind = self#get_akind ()in
    let error = self#get_visit_error () in
    let env = Process.Env.create kf kinstr akind in
    Process.predicate ?error env p;
    Cil.SkipChildren

  (** Launch the analysis on the given term. *)
  method !vterm t =
    let kf = Option.get self#current_kf in
    let kinstr = self#current_kinstr in
    let akind = self#get_akind ()in
    let error = self#get_visit_error () in
    let env = Process.Env.create kf kinstr akind in
    Process.term ?error env t;
    Cil.SkipChildren

end

let preprocess ast =
  let vis = new vis_at_labels () in
  vis#visit_file ast;
  preprocess_done := true

let reset () =
  preprocess_done := false;
  Stmt.Hashtbl.clear at_data_for_stmts

let _debug () =
  Options.feedback ~level:2 "Labels preprocessing";
  Options.feedback ~level:2 "|Locations:";
  Stmt.Hashtbl.iter
    (fun stmt ats_ref ->
       Options.feedback ~level:2 "| - stmt %d at %a"
         stmt.sid
         Printer.pp_location (Stmt.loc stmt);
       At_data.Set.iter
         (fun at ->
            Options.feedback ~level:2 "|    - at %a"
              At_data.pretty at)
         !ats_ref
    )
    at_data_for_stmts

(*
Local Variables:
compile-command: "make -C ../../../../.."
End:
*)
