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
open Analyses_types

(**************************************************************************)
(********************** Forward references ********************************)
(**************************************************************************)

let must_translate_ppt_ref : (Property.t -> bool) ref =
  Extlib.mk_fun "must_translate_ppt_ref"

let must_translate_ppt_opt_ref : (Property.t option -> bool) ref =
  Extlib.mk_fun "must_translate_ppt_opt_ref"

(**************************************************************************)
(************************* Case globals ***********************************)
(**************************************************************************)

let case_globals
    ~default
    ?(builtin = fun _ -> default ())
    ?(fc_compiler_builtin = fun _ -> default ())
    ?(rtl_symbol = fun _ -> default ())
    ?(fc_stdlib_generated = fun _ -> default ())
    ?(var_fun_decl = fun _ -> default ())
    ?(var_init = fun _ -> default ())
    ?(var_def = fun _ _ -> default ())
    ?(glob_annot = fun _ -> default ())
    ~fun_def
  = function
    (* library functions and built-ins *)
    | GVarDecl(vi, _) | GVar(vi, _, _)
    | GFunDecl(_, vi, _) | GFun({ svar = vi }, _) when Builtins.mem vi.vname ->
      builtin vi

    (* Cil built-ins and other library globals*)
    | GVarDecl(vi, _) | GVar(vi, _, _) | GFun({ svar = vi }, _)
      when Misc.is_fc_or_compiler_builtin vi ->
      fc_compiler_builtin vi

    | g when Rtl.Symbols.mem_global g ->
      rtl_symbol g

    (* generated function declaration *)
    | GFunDecl(_, vi, _) when Misc.is_fc_stdlib_generated vi ->
      fc_stdlib_generated vi

    (* variable declarations *)
    | GVarDecl(vi, _) | GFunDecl(_, vi, _) ->
      var_fun_decl vi

    (* variable definition *)
    | GVar(vi, { init = None }, _) ->
      var_init vi

    | GVar(vi, { init = Some init }, _) ->
      var_def vi init

    (* function definition *)
    | GFun(fundec, _) ->
      fun_def fundec

    (* global annotation *)
    | GAnnot (ga, _) ->
      glob_annot ga

    (* other globals: nothing to do *)
    | GType _
    | GCompTag _
    | GCompTagDecl _
    | GEnumTag _
    | GEnumTagDecl _
    | GAsm _
    | GPragma _
    | GText _
      ->
      default ()

(**************************************************************************)
(****************************** Visitor ***********************************)
(**************************************************************************)

class visitor cat
  = object(self)
    inherit Visitor.frama_c_inplace

    (* Functions for [case_globals] *)
    (* ---------------------------- *)

    method private default : unit -> global list Cil.visitAction =
      fun _ -> Cil.SkipChildren

    method builtin : varinfo -> global list Cil.visitAction =
      fun _ -> self#default ()

    method fc_compiler_builtin : varinfo -> global list Cil.visitAction =
      fun _ -> self#default ()

    method rtl_symbol : global -> global list Cil.visitAction =
      fun _ -> self#default ()

    method fc_stdlib_generated : varinfo -> global list Cil.visitAction =
      fun _ -> self#default ()

    method var_fun_decl : varinfo -> global list Cil.visitAction =
      fun _ -> self#default ()

    method var_init : varinfo -> global list Cil.visitAction =
      fun _ -> self#default ()

    method var_def : varinfo -> init -> global list Cil.visitAction =
      fun _ _ -> self#default ()

    method glob_annot: global_annotation -> global list Cil.visitAction =
      fun _ -> Cil.DoChildren (* do visit ACSL annotations by default *)

    method fun_def ({svar = vi}) =
      let kf = try Globals.Functions.get vi with Not_found -> assert false in
      if Functions.check kf then Cil.DoChildren else Cil.SkipChildren

    (* Visit error *)
    (* ----------- *)

    (** Error module to use when creating E-ACSL errors. *)
    val error_module: (module Error.S) =
      (module Error.Make(struct let phase = cat end): Error.S)

    (** Visit error *)
    val mutable visit_error: exn option = None

    (** Reset the visit error to [None], or [force] if it is provided. *)
    method private reset_visit_error ?force:visit_error_opt () =
      match visit_error_opt with
      | Some visit_error_opt -> visit_error <- visit_error_opt
      | None -> visit_error <- None

    (** Set the visit error to [e] if it was [None], keep the existing visit
        error otherwise. *)
    method private set_visit_error e =
      match visit_error with
      | None -> visit_error <- Some e
      | Some _ -> ()

    (** @return the current visit error. *)
    method get_visit_error () = visit_error

    (* Annotation kind *)
    (* --------------- *)

    (** Annotation kind *)
    val mutable akind: annotation_kind = Assertion

    (** Set the annotation kind to [a]. *)
    method private set_akind a = akind <- a

    (** @return the current annotation kind. *)
    method get_akind () = akind

    (* Starting AST visits *)
    (* ------------------- *)

    (** Indicates if the current visit has been run from this visitor (with
        [visit_xxx] methods) or from a generic [Visitor.visitFramacxxx]
        function.
        If this boolean is [false] when passing through the methods [vspec]
        or [vcode_annot], then a fatal error is raised because the children will
        be skipped without the knowledge of the caller. *)
    val mutable run_from_visitor: bool = false

    (** If [true], the method [vcode_annot] will visit its children, otherwise
        they are skipped. *)
    val mutable do_visit_code_annot: bool = false

    (** If [true], the method [vspec] will visit its children, otherwise they
        are skipped. *)
    val mutable do_visit_spec: bool = false

    (** Set the [run_from_visitor] field to [value] and return its old value. *)
    method private set_run_from_visitor value =
      let old = run_from_visitor in
      run_from_visitor <- value;
      old

    (** Check if [run_from_visitor] is [true], otherwise raise a fatal error. *)
    method private check_run_from_visitor () =
      if not run_from_visitor then
        Options.fatal
          "E_acsl_visitors should be run with methods 'visit_xyz' to correctly \
           visit each node."

    (** If [value_opt] is [Some value], then set field [do_visit_code_annot] to
        [value] and return the old value of [do_visit_code_annot] in an option.
        Otherwise do nothing and return [None]. *)
    method private set_do_visit_code_annot value_opt =
      match value_opt with
      | Some value ->
        let old = do_visit_code_annot in
        do_visit_code_annot <- value;
        Some old
      | None -> None

    (** If [value_opt] is [Some value], then set field [do_visit_spec] to
        [value] and return the old value of [do_visit_spec] in an option.
        Otherwise do nothing and return [None]. *)
    method private set_do_visit_funspec value_opt =
      match value_opt with
      | Some value ->
        let old = do_visit_spec in
        do_visit_spec <- value;
        Some old
      | None -> None

    (* see documentation in e_acsl_visitor.mli *)
    method visit
      : 'a 'b. ?vcode_annot:bool -> ?vspec:bool
        -> (Visitor.frama_c_visitor -> 'a -> 'b)
        -> 'a -> 'b
      = fun ?vcode_annot ?vspec visit_func item ->
        let old_run_from_visitor = self#set_run_from_visitor true in
        let old_vcode_annot = self#set_do_visit_code_annot vcode_annot in
        let old_vfunspec = self#set_do_visit_funspec vspec in
        let finally () =
          ignore @@ self#set_do_visit_code_annot old_vcode_annot;
          ignore @@ self#set_do_visit_funspec old_vfunspec;
          ignore @@ self#set_run_from_visitor old_run_from_visitor
        in
        Extlib.try_finally
          ~finally
          (fun item -> visit_func (self :> Visitor.frama_c_inplace) item)
          item

    (** see documentation in e_acsl_visitor.mli *)
    method visit_file file =
      self#visit Visitor.visitFramacFileSameGlobals file

    (** see documentation in e_acsl_visitor.mli *)
    method visit_code_annot code_annot =
      self#visit ~vcode_annot:true Visitor.visitFramacCodeAnnotation code_annot

    (** [visit_assigns assigns] starts a visit of the AST from the given
        [assigns] node. *)
    method private visit_assigns assigns =
      (* private method, we do not need to use self#visit, the field
         [run_from_visitor] is already set. *)
      ignore @@ Visitor.visitFramacAssigns
        (self :> Visitor.frama_c_inplace)
        assigns

    (** [visit_allocates allocates] starts a visit of the AST from the given
        [allocation] node. *)
    method private visit_allocates allocates =
      (* private method, we do not need to use self#visit, the field
         [run_from_visitor] is already set. *)
      ignore @@ Visitor.visitFramacAllocation
        (self :> Visitor.frama_c_inplace)
        allocates

    (** [visit_id_predicate idp] starts a visit of the AST from the given
        [identified_predicate] node. *)
    method private visit_id_predicate idp =
      (* private method, we do not need to use self#visit, the field
         [run_from_visitor] is already set. *)
      ignore @@ Visitor.visitFramacIdPredicate
        (self :> Visitor.frama_c_inplace)
        idp

    (** [visit_id_predicates idps] starts a visit of the AST for each given
        [identified_predicate] node. *)
    method private visit_id_predicates idps =
      (* private method, we do not need to use self#visit, the field
         [run_from_visitor] is already set. *)
      List.iter
        self#visit_id_predicate
        idps

    (** see documentation in e_acsl_visitor.mli *)
    method visit_predicate p =
      (* We know that from a predicate node, we will not use the visit methods
         [vcode_annot] and [vspec], so we do not need to use [self#visit].
         This saves us some indirection when calling
         [Visitor.visitFramacPredicate]. *)
      Visitor.visitFramacPredicate (self :> Visitor.frama_c_inplace) p

    (** [visit_term t] starts a visit of the AST from the given [term] node. *)
    method private visit_term t =
      (* private method, we do not need to use self#visit, the field
         [run_from_visitor] is already set. *)
      ignore @@ Visitor.visitFramacTerm (self :> Visitor.frama_c_inplace) t

    (* Override visit methods *)
    (* ---------------------- *)

    (** [do_with ?not_yet ?akind ~f arg] changes the visit error to [not_yet]
        and changes the annotation kind to [akind] if provided, then execute
        [f arg]. Finally, it restores the visit error and annotation kind to
        their old values and returns the result of [f arg]. *)
    method private do_with: 'a 'b.
      ?not_yet:string ->
      ?akind:annotation_kind ->
      f:('a -> 'b) ->
      'a ->
      'b
      =
      fun ?not_yet ?akind ~f arg ->
      let module Error = (val error_module: Error.S) in
      let old_akind = self#get_akind () in
      let old_visit_error = self#get_visit_error () in
      (match akind with
       | Some akind -> self#set_akind akind
       | None -> ());
      (match not_yet with
       | Some not_yet -> self#set_visit_error (Error.make_not_yet not_yet)
       | None -> ());
      let finally () =
        self#reset_visit_error ~force:old_visit_error ();
        self#set_akind old_akind
      in
      Extlib.try_finally ~finally f arg

    (** [process_spec spec] visits the given [spec] in the same manner than
        the E-ACSL injector, setting the annotation kind to its correct value as
        it visits the different nodes. *)
    method private process_spec spec =
      let kf = Option.get self#current_kf in
      let kinstr = self#current_kinstr in
      List.iter
        (fun bhv ->
           self#do_with
             ~akind:Precondition
             ~f:self#visit_id_predicates
             bhv.b_assumes;
           self#do_with
             ~akind:Precondition
             ~f:(List.iter
                   (fun requires ->
                      if !must_translate_ppt_ref
                          (Property.ip_of_requires kf kinstr bhv requires) then
                        self#visit_id_predicate requires))
             bhv.b_requires;
           (* The links between the [identified_property]s and the [assigns] or
              [allocates] clauses are not clear. For now, store a [not_yet]
              error for every term of the clauses. Update the code to add the
              relevant [must_translate] calls once the [assigns] or [allocates]
              clauses translation are supported. *)
           self#do_with
             ~akind:Postcondition
             ~not_yet:"assigns clause in behavior"
             ~f:self#visit_assigns
             bhv.b_assigns;
           self#do_with
             ~akind:Postcondition
             ~not_yet:"allocates clause in behavior"
             ~f:self#visit_allocates
             bhv.b_allocation;
           List.iter
             (fun ((termination, post_cond) as tp) ->
                if !must_translate_ppt_ref
                    (Property.ip_of_ensures kf kinstr bhv tp) then
                  let not_yet =
                    match termination with
                    | Normal ->
                      None
                    | Exits | Breaks | Continues | Returns ->
                      Some "abnormal termination case in behavior"
                  in
                  self#do_with
                    ~akind:Postcondition
                    ?not_yet
                    ~f:self#visit_id_predicate
                    post_cond)
             bhv.b_post_cond
        )
        spec.spec_behavior

    (** [set_global_kinstr ()] sets the [current_kinstr] field of the visitor
        to [Kglobal] and returns the old value of [current_kinstr]. This
        function is used in [vstmt_aux] to process the function specification
        with a [current_kinstr] correctly set. *)
    method private set_global_kinstr () =
      let rec aux acc =
        match self#current_stmt with
        | Some stmt ->
          self#pop_stmt stmt;
          aux (stmt :: acc)
        | None ->
          acc
      in
      aux []

    (** [reset_kinstr stmts] resets the [current_kinstr] field of the visitor
        to the given statement list. The list given as parameter is the value
        returned by [set_global_kinstr ()]. *)
    method private reset_kinstr stmts =
      List.iter
        (fun stmt -> self#push_stmt stmt)
        stmts

    (** Visit AST globals according to the provided methods. *)
    method !vglob_aux =
      case_globals
        ~default:self#default
        ~builtin:self#builtin
        ~fc_compiler_builtin:self#fc_compiler_builtin
        ~rtl_symbol:self#rtl_symbol
        ~fc_stdlib_generated:self#fc_stdlib_generated
        ~var_fun_decl:self#var_fun_decl
        ~var_init:self#var_init
        ~var_def:self#var_def
        ~glob_annot:self#glob_annot
        ~fun_def:self#fun_def

    (** Visit the annotations of the statement in the same manner than the
        E-ACSL injector. *)
    method! vstmt_aux stmt =
      let kf = Option.get self#current_kf in

      if Kernel_function.is_first_stmt kf stmt then begin
        (* Analyze the funspec before visiting the first statement *)
        if Annotations.has_funspec kf then begin
          let old_kinstr_stmts = self#set_global_kinstr () in
          self#process_spec (Annotations.funspec kf);
          self#reset_kinstr old_kinstr_stmts
        end
      end;

      (* Analyze the code annotation of the current statement *)
      Annotations.iter_code_annot
        (fun _ annot ->
           (* Reset the visit error before starting to analyze an annotation. *)
           self#reset_visit_error ();

           match annot.annot_content with
           | AAssert(l, p) ->
             if !must_translate_ppt_ref
                 (Property.ip_of_code_annot_single kf stmt annot) then begin
               let not_yet =
                 match l with
                 | [] -> None
                 | _ :: _ -> Some "assertion applied only on some behaviors"
               in
               ignore @@ self#do_with
                 ~akind:Assertion
                 ?not_yet
                 ~f:self#visit_predicate
                 p.tp_statement
             end
           | AStmtSpec(l, spec) ->
             let not_yet =
               match l with
               | [] -> None
               | _ :: _ ->
                 Some "statement contract applied only on some behaviors"
             in
             self#do_with
               ?not_yet
               ~f:self#process_spec
               spec
           | AInvariant(l, _, p) ->
             if !must_translate_ppt_ref
                 (Property.ip_of_code_annot_single kf stmt annot) then begin
               let not_yet =
                 match l with
                 | [] -> None
                 | _ :: _ -> Some "invariant applied only on some behaviors"
               in
               ignore @@ self#do_with
                 ~akind:Invariant
                 ?not_yet
                 ~f:self#visit_predicate
                 p.tp_statement
             end
           | AVariant(t, _) ->
             if !must_translate_ppt_ref
                 (Property.ip_of_code_annot_single kf stmt annot) then begin
               self#do_with
                 ~akind:Variant
                 ~f:self#visit_term
                 t
             end
           | AAssigns (_, assigns) ->
             (* The link between the [identified_property] and the [assigns]
                clause is not clear. For now store a [not_yet] error for every
                term of the clause. Update the code to add the relevant
                [must_translate] calls once the [assigns] clause translation is
                supported. *)
             self#do_with
               ~akind:Postcondition
               ~not_yet:"assigns"
               ~f:self#visit_assigns
               assigns
           | AAllocation (_, allocates) ->
             (* The link between the [identified_property] and the [allocates]
                clause is not clear. For now store a [not_yet] error for every
                term of the clause. Update the code to add the relevant
                [must_translate] calls once the [allocates] clause translation
                is supported. *)
             self#do_with
               ~akind:Postcondition
               ~not_yet:"allocates"
               ~f:self#visit_allocates
               allocates
           | APragma _ -> ()
           | AExtended _ -> ()
        )
        stmt;

      (* Once the annotations of the statements have been analyzed, reset the
         visit error. *)
      self#reset_visit_error ();

      Cil.DoChildren

    (** [vspec spec] visits its children if [do_visit_spec] is [true] and skips
        them otherwise. *)
    method! vspec _ =
      self#check_run_from_visitor ();
      if do_visit_spec then
        Cil.DoChildren
      else
        Cil.SkipChildren

    (** [vcode_annot ca] visits its children if [do_visit_code_annot] is [true]
        and skips them otherwise. *)
    method! vcode_annot _ =
      self#check_run_from_visitor ();
      if do_visit_code_annot then
        Cil.DoChildren
      else
        Cil.SkipChildren

  end
