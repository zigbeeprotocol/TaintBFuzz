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

(** Module for preprocessing the quantified predicates. Predicates with
    quantifiers are hard to translate, so we delegate some of the work to
    a preprocessing phase. At the end of this phase, all the quantified
    predicates should have an associated preprocessed form [vars * goal] where
    - [vars] is a list of guarded variables in the right order
    - [goal] is the predicate under the quantifications
      The guarded variables in the list [vars] are of
      type [term * logic_var * term * predicate option], where a tuple
      [(t1,v,t2,p)] indicates that v is a logic variable with the two
      guards t1 <= x < t2 and p is an additional optional guard to
      intersect the first guard with the provided type for the variable v
*)
open Cil_types
open Cil_datatype

let dkey = Options.Dkey.bound_variables
module Error = Error.Make(struct let phase = dkey end)

(** [error_msg quantif msg pp x] creates an error message from the string [msg]
    containing the value [x] pretty-printed by [pp] and the predicate [quantif]
    pretty-printed. *)
let error_msg quantif msg pp x =
  let msg1 = Format.asprintf msg pp x in
  let msg2 =
    Format.asprintf "@[ in quantification@ %a@]"
      Printer.pp_predicate quantif
  in
  msg1 ^ msg2

(** A module to work with quantifiers at preprocessing time. We create
    a datatype to hash quantified predicates by simply giving the hash
    of their first variable.
*)
module Quantified_predicate =
  Datatype.Make_with_collections
    (struct
      include Cil_datatype.Predicate
      let name = "E_ACSL.Quantified_predicate"
      let hash (p:predicate) = match p.pred_content with
        | Pforall(lvs,_)
        | Pexists(lvs,_) ->
          begin match lvs with
            |[] -> 0
            |lv::_ -> Cil_datatype.Logic_var.hash lv
          end
        | _ -> assert false
      (* The function compare should never be used since we only use this
         datatype for hashtables *)
      let compare _ _ = assert false
      let equal (p1:predicate) p2 = p1 == p2
      let structural_descr = Structural_descr.t_abstract
      let rehash = Datatype.identity
      let mem_project = Datatype.never_any_project
    end)

(****************************************************************************)
(** Storing the preprocessed quantifiers *)
(****************************************************************************)

(* Memoization module to store the preprocessed form of a quantified predicate
*)
module Quantifier: sig
  val add:
    predicate ->
    ((term * logic_var * term) list * predicate) Error.result ->
    unit
  val get:
    predicate ->
    ((term * logic_var * term) list * predicate) Error.result

  (** getter and setter for the additional guard that intersects with the type
      of the variable *)
  val get_guard_for_small_type : logic_var -> predicate option
  val add_guard_for_small_type : logic_var -> predicate -> unit
  val replace : predicate -> (term * logic_var * term) list -> predicate -> unit
  val clear : unit -> unit
end = struct

  let tbl = Quantified_predicate.Hashtbl.create 97

  let guard_tbl = Cil_datatype.Logic_var.Hashtbl.create 97

  let get p =
    try Quantified_predicate.Hashtbl.find tbl p
    with Not_found -> Error.not_memoized ()

  let add p res_or_error =
    Quantified_predicate.Hashtbl.add tbl p res_or_error

  let get_guard_for_small_type x =
    try Some (Cil_datatype.Logic_var.Hashtbl.find guard_tbl x)
    with Not_found -> None

  let add_guard_for_small_type lv p =
    Cil_datatype.Logic_var.Hashtbl.add guard_tbl lv p

  let replace p guarded_vars goal =
    Quantified_predicate.Hashtbl.replace tbl p (Result.Ok (guarded_vars, goal))

  let clear () =
    Cil_datatype.Logic_var.Hashtbl.clear guard_tbl;
    Quantified_predicate.Hashtbl.clear tbl
end

(** Getters and setters *)
let get_preprocessed_quantifier = Quantifier.get
let get_guard_for_small_type = Quantifier.get_guard_for_small_type
let add_guard_for_small_type = Quantifier.add_guard_for_small_type
let replace = Quantifier.replace
let clear_guards = Quantifier.clear

(** Helper module to process the constraints in the quantification and extract
    guards for the quantified variables. *)
module Constraints: sig
  (** Context type manipulated by the functions of the module. *)
  type t

  (** [empty quantif bounded_vars] creates an empty context from a
      quantification predicate and the list of bounded variables for the
      predicate. *)
  val empty: predicate -> logic_var list -> t

  (** [get_bounded_var ctxt t] returns the logic var corresponding to the given
      term if the term is a variable ([TLval(Tvar _, TNoOffset)]) that is a
      bounded variable for the quantification being processed, or [None]
      otherwise. *)
  val get_bounded_var: term -> t -> logic_var option

  (** [has_unguarded_bounded_vars ctxt] returns true iff some bounded variables
      in [ctxt] do not have a guard extracted from the quantification
      predicate. *)
  val has_unguarded_bounded_vars: t -> bool

  (** [add_lower_bound ctxt t r lv] adds the lower bound [t r lv] to the list
      of guards for the quantification.
      @raises Typing_error if a lower bound already exists for [lv]. *)
  val add_lower_bound: term -> relation -> logic_var -> t -> t

  (** [add_linked_upper_bound ctxt lv1 r lv2] adds a link between two bounded
      variables with still incomplete guards. [lv1] should already have at least
      a lower bound.
      @raises Typing_error if [lv1] do not have an existing lower bound. *)
  val add_linked_upper_bound: logic_var -> relation -> logic_var -> t -> t

  (** [add_upper_bound ctxt lv r t] adds the upper bound [lv r t] to the list of
      guards for the quantification.
      For each existing linked relation [lv' r' lv], also adds the upper bound
      [lv' r'' t] to the list of guards, with [r''] being the strictest relation
      between [r] and [r'].
      @raises Typing_error if either [lv] or [lv'] does not have an existing
      lower bound. *)
  val add_upper_bound: logic_var -> relation -> term -> t -> t

  (** [check_validity ctxt] checks the validity of the quantification after
      processing.
      @raises Typing_error if some bound (lower or upper) cound not be extracted
      from the quantification for each bounded variable. *)
  val check_validity: t -> unit

  (** [retrieve_guards ctxt] returns the list of guards for the bounded
      variables of the quantification, in the order in which they must be
      generated, ie. if [j] depends on [i] then the guard for [i] will be before
      the guard for [j] in the list.
      [check_validity ctxt] must have been called before calling
      [retrieve_guards]. *)
  val retrieve_guards: t -> (term * relation * logic_var * relation * term) list

  (** [raise_error ctxt msg] raises a [Typing_error] exception with the given
      message after appending the quantification from the context. *)
  val raise_error: string -> t -> 'a

  (** [error_invalid_pred ?warn_rel ctxt p] raises a [Typing_error] exception
      with a message indicating that the predicate [p] is not valid in the
      quantification. Depending on the state of [ctxt], more information about
      missing bounds is added to the message. If [warn_rel] is [true], then a
      reminder that only [Rle] and [Rlt] are allowed to guard quantified
      variables is added to the message. *)
  val raise_error_invalid_pred: ?warn_rel:bool -> predicate -> t -> 'a
end = struct
  type t = {
    quantif: predicate;
    (** Quantification predicate being analyzed. *)
    bounded_vars: Logic_var.Set.t;
    (** Variables of the quantification that still need guards. *)
    rev_order: Logic_var.t list;
    (** Bounded variables list in reverse order in which they must be
        generated. *)
    guards: (term * relation * (relation * term) option) Logic_var.Map.t;
    (** Table associating a bounded variable with its guard. *)
    linked_upper_bounds: (logic_var * relation) Logic_var.Map.t;
    (** Table associating a bounded variable with a relation with another
        bounded variable. *)
  }

  let empty quantif bounded_vars =
    (* Check that the bounded vars have integer type and store them in a set. *)
    let bounded_vars =
      List.fold_left
        (fun s v ->
           let v =
             match v.lv_type with
             | Ctype ty when Cil.isIntegralType ty -> v
             | Linteger -> v
             | Ltype _ as ty when Logic_const.is_boolean_type ty -> v
             | Ctype _ | Ltype _ | Lvar _ | Lreal | Larrow _ ->
               Error.not_yet
                 (error_msg
                    quantif
                    "@[non integer variable %a@]"
                    Printer.pp_logic_var v)
           in
           Logic_var.Set.add v s
        )
        Logic_var.Set.empty
        bounded_vars
    in
    {
      quantif;
      bounded_vars;
      rev_order = [];
      guards = Logic_var.Map.empty;
      linked_upper_bounds = Logic_var.Map.empty;
    }

  let get_bounded_var t ctxt =
    let rec aux t =
      match t.term_node with
      | TLogic_coerce(_, t) -> aux t
      | TLval(TVar lv, TNoOffset) when Logic_var.Set.mem lv ctxt.bounded_vars ->
        Some lv
      | _ -> None
    in
    aux t

  let has_unguarded_bounded_vars ctxt =
    not (Logic_var.Set.is_empty ctxt.bounded_vars)

  (** Pretty printer for a guard, represented by a tuple
      [(term, relation, logic_var, relation, term)]. *)
  let pp_guard fmt (t1, r1, lv, r2, t2) =
    Format.fprintf
      fmt
      "@[%a %a %a %a %a@]"
      Printer.pp_term t1
      Printer.pp_relation r1
      Printer.pp_logic_var lv
      Printer.pp_relation r2
      Printer.pp_term t2

  (** Pretty printer for a lower bound, represented by the tuple
      [(term, relation, logic_var)]. *)
  let pp_lbound fmt (t, r, lv) =
    Format.fprintf
      fmt
      "@[%a %a %a@]"
      Printer.pp_term t
      Printer.pp_relation r
      Printer.pp_logic_var lv

  (** Pretty printer for a bound between two quantified variables,
      represented by the tuple [(logic_var, relation, logic_var)]. *)
  let pp_linked_bound fmt (lv1, r, lv2) =
    Format.fprintf
      fmt
      "@[%a %a %a@]"
      Printer.pp_logic_var lv1
      Printer.pp_relation r
      Printer.pp_logic_var lv2

  let add_lower_bound t r lv ctxt =
    match Logic_var.Map.find_opt lv ctxt.guards with
    | None ->
      { ctxt with
        guards = Logic_var.Map.add lv (t, r, None) ctxt.guards; }
    | Some (t', r', None) ->
      let msg =
        Format.asprintf
          "@[found existing lower bound %a@ when processing %a@ \
           in quantification@ %a@]"
          pp_lbound (t', r', lv)
          pp_lbound (t, r, lv)
          Printer.pp_predicate ctxt.quantif
      in
      Error.untypable msg
    | Some (t1', r1', Some (r2', t2')) ->
      let msg =
        Format.asprintf
          "@[found existing guard %a@ when processing %a@ \
           in quantification@ %a@]"
          pp_guard (t1', r1', lv, r2', t2')
          pp_lbound (t, r, lv)
          Printer.pp_predicate ctxt.quantif
      in
      Error.untypable msg

  let add_linked_upper_bound lv1 r lv2 ctxt =
    if Logic_var.Map.mem lv1 ctxt.guards then begin
      { ctxt with
        linked_upper_bounds =
          Logic_var.Map.add lv2
            (lv1, r)
            ctxt.linked_upper_bounds; }
    end else
      let msg=
        Format.asprintf
          "@[missing lower bound for %a@ when processing the linked upper \
           bound %a@ in quantification@ %a@]"
          Printer.pp_logic_var lv1
          pp_linked_bound (lv1, r, lv2)
          Printer.pp_predicate ctxt.quantif
      in
      Error.untypable msg

  let add_upper_bound lv r t ctxt =
    (* Select the strictest relation between [r1] and [r2], with both relations
       being either [Rlt] or [Rle]. *)
    let strictest_relation r1 r2 =
      match r1, r2 with
      | (Rlt | Rle), Rlt | Rlt, Rle -> Rlt
      | Rle, Rle -> Rle
      | _, _ ->
        Options.fatal
          "invalid relations %a and %a in quantification %a"
          Printer.pp_relation r1
          Printer.pp_relation r2
          Printer.pp_predicate ctxt.quantif
    in
    (* Replace the guard for [lv] to add the upper bound [lv r t], and
       recursively walk the bounds linked to [lv] to also add upper bounds. *)
    let rec replace_guard lv r t ctxt =
      try
        let lower_bound_t, lower_bound_r, _ =
          Logic_var.Map.find lv ctxt.guards
        in
        let ctxt =
          { ctxt with
            guards =
              Logic_var.Map.add
                lv
                (lower_bound_t, lower_bound_r, Some (r, t))
                ctxt.guards; }
        in
        let ctxt =
          { ctxt with
            bounded_vars = Logic_var.Set.remove lv ctxt.bounded_vars; }
        in
        let need_upper_bound =
          Logic_var.Map.find_opt lv ctxt.linked_upper_bounds
        in
        let ctxt =
          match need_upper_bound with
          | Some (lv', r') ->
            let ctxt =
              { ctxt with
                linked_upper_bounds =
                  Logic_var.Map.remove lv ctxt.linked_upper_bounds; }
            in
            replace_guard lv' (strictest_relation r r') t ctxt
          | None -> ctxt
        in
        { ctxt with rev_order = lv :: ctxt.rev_order }
      with Not_found ->
        Error.untypable
          (error_msg ctxt.quantif
             "@[missing lower bound for %a@]"
             Printer.pp_logic_var lv)
    in
    replace_guard lv r t ctxt

  let check_validity ctxt =
    if not (Logic_var.Map.is_empty ctxt.linked_upper_bounds) then
      let msg =
        let iter_keys f map_seq =
          Seq.iter
            (fun (key, _) -> f key)
            map_seq
        in
        Format.asprintf
          "@[missing upper bound%s for %a@ in quantification@ %a@]"
          (if Logic_var.Map.cardinal ctxt.linked_upper_bounds = 1 then ""
           else "s")
          (Pretty_utils.pp_iter
             ~sep:", "
             iter_keys
             Printer.pp_logic_var)
          (Logic_var.Map.to_seq ctxt.linked_upper_bounds)
          Printer.pp_predicate ctxt.quantif
      in
      Error.untypable msg
    else if not (Logic_var.Set.is_empty ctxt.bounded_vars) then
      let msg =
        Format.asprintf
          "@[missing lower bound%s for %a@ in quantification@ %a@]"
          (if Logic_var.Set.cardinal ctxt.bounded_vars = 1 then "" else "s")
          (Pretty_utils.pp_iter
             ~sep:", "
             Logic_var.Set.iter
             Printer.pp_logic_var)
          ctxt.bounded_vars
          Printer.pp_predicate ctxt.quantif
      in
      Error.untypable msg

  let retrieve_guards ctxt =
    List.fold_left
      (fun acc lv ->
         match Logic_var.Map.find_opt lv ctxt.guards with
         | Some (t1, r1, Some (r2, t2)) ->
           (t1, r1, lv, r2, t2) :: acc

         (* The error cases should not occur if the traversal of the
            quantification was completed and [check_validity] was called
            successfully. *)
         | Some (_, _, None) ->
           Options.fatal
             "Missing upper bound when trying to retrieve the guard for %a"
             Printer.pp_logic_var lv
         | None -> Options.fatal "Missing guard for %a" Printer.pp_logic_var lv
      )
      []
      ctxt.rev_order

  let raise_error msg ctxt =
    let msg2 =
      Format.asprintf "@[ in quantification@ %a@]"
        Printer.pp_predicate ctxt.quantif
    in
    Error.untypable (msg ^ msg2)

  let raise_error_invalid_pred ?(warn_rel=false) p ctxt =
    (* Extract the set of variables that have another variable for upper bound.
       They will be considered valid for the purpose of the error message, ie.
       if we have the relation [0 < i < j] with [0 < i] as an incomplete guard
       and [i < j] as a linked upper bound, then the error is about [j] not
       having an upper bound, not about [i]. *)
    let linked_upper_bounds =
      Logic_var.Map.fold
        (fun _ (lv, _) acc -> Logic_var.Set.add lv acc)
        ctxt.linked_upper_bounds
        Logic_var.Set.empty
    in

    let missing_guards, missing_upper_bounds =
      Logic_var.Set.fold
        (fun lv (missing_guards, missing_upper_bounds) ->
           match Logic_var.Map.find_opt lv ctxt.guards with
           | Some (_, _, None)
             when not (Logic_var.Set.mem lv linked_upper_bounds) ->
             (* A variable with an incomplete constraint and without a linked
                upper bound has a missing upper bound. *)
             missing_guards, lv :: missing_upper_bounds
           | None ->
             (* A variable without a constraint has a missing guard. *)
             lv :: missing_guards, missing_upper_bounds
           | _ ->
             (* Otherwise the variable either has a complete constraint, or an
                incomplete constraint but with a linked upper bound. *)
             missing_guards, missing_upper_bounds)
        ctxt.bounded_vars
        ([], [])
    in

    let msg =
      Format.asprintf
        "@[invalid guard %a@ in quantification@ %a.@ \
         %a@,%a@ \
         %t@]"
        Printer.pp_predicate p Printer.pp_predicate ctxt.quantif
        (Pretty_utils.pp_list
           ~pre:"@[Missing guard for "
           ~sep:",@ "
           ~suf:".@]"
           Printer.pp_logic_var)
        (List.rev missing_guards)
        (Pretty_utils.pp_list
           ~pre:"@[Missing upper bound for "
           ~sep:",@ "
           ~suf:".@]"
           Printer.pp_logic_var)
        (List.rev missing_upper_bounds)
        (fun fmt ->
           if warn_rel then
             Format.fprintf fmt
               "@[Only %a and %a are allowed to guard quantifier variables@]"
               Printer.pp_relation Rlt Printer.pp_relation Rle)
    in
    Error.untypable msg

end

(******************************************************************************)
(** Syntactical analysis *)
(******************************************************************************)

(** [extract_constraint ctxt t1 r t2] populates the quantification context
    [ctxt] with the constraint [t1 r t2], either adding a lower bound if [t2] is
    a bounded variable or adding an upper bound if [t1] is a bounded variable.
    @raises Typing_error if no constraint can be extracted or if the constraint
    is invalid (no bounded variable in [t1] or [t2] for instance). *)
let extract_constraint ctxt t1 r t2 =
  (* Return the logic var corresponding to the given term or [None] if the term
     is not a variable ([TLval(TVar _, TNoOffset)]). *)
  let rec _get_logic_var_opt t =
    match t.term_node with
    | TLogic_coerce(_, t) -> _get_logic_var_opt t
    | TLval(TVar x, TNoOffset) -> Some x
    | _ -> None
  in
  (* Process the given relation *)
  let lv1 = Constraints.get_bounded_var t1 ctxt in
  let lv2 = Constraints.get_bounded_var t2 ctxt in
  match lv1, lv2 with
  | None, Some lv2 -> (* t1 value, t2 variable: store lower bound *)
    Constraints.add_lower_bound t1 r lv2 ctxt
  | Some lv1, None -> (* t1 variable, t2 value: store upper bound *)
    Constraints.add_upper_bound lv1 r t2 ctxt
  | Some lv1, Some lv2 ->
    (* t1 variable, t2 variable: store link between t1 and t2 *)
    let ctxt = Constraints.add_linked_upper_bound lv1 r lv2 ctxt in
    Constraints.add_lower_bound t1 r lv2 ctxt
  | None, None -> (* t1 value, t2 value: error *)
    let msg =
      Format.asprintf
        "@[invalid constraint %a %a %a, both operands are constants or \
         already bounded@]"
        Printer.pp_term t1
        Printer.pp_relation r
        Printer.pp_term t2
    in
    Constraints.raise_error msg ctxt

(** [visit_quantif_relations ~is_forall ctxt p] traverses the predicate [p] of
    the quantification being analyzed in the context [ctxt] from left to right
    as long as the predicate is [Pimplies], [Pand] or [Prel(Rlt | Rle)], and
    calls [extract_constraint] on each relation [Rlt] or [Rle] it encounters
    until all the guards of the quantification have been found or the predicate
    is finished. If [is_forall] is [true] then the predicate being traversed is
    a universal quantification, otherwise it is an existential quantification.
    The function returns a tuple [ctxt, goal_opt] where [ctxt] is the
    quantification context and [goal_opt] is either [None] if the goal of the
    quantification has not been found yet or [Some goal] if [goal] is the
    predicate corresponding to the goal of the quantification.
    @raises Typing_error if the predicate contains something other than
    [Pimplies], [Pand] or [Prel] with a relation that is neither [Rlt] nor
    [Rle]. *)
let rec visit_quantif_relations ~is_forall ctxt p =
  match p.pred_content with
  | Pimplies(lhs, rhs) ->
    let ctxt, _ = visit_quantif_relations ~is_forall ctxt lhs in
    if is_forall then begin
      if Constraints.has_unguarded_bounded_vars ctxt then
        visit_quantif_relations ~is_forall ctxt rhs
      else
        ctxt, Some rhs
    end else
      let msg =
        Format.asprintf
          "@[invalid quantification guard, expecting '%s' to continue@ \
           bounding variables,@ found '%s'@]"
          (if Kernel.Unicode.get () then Utf8_logic.conj else "&&")
          (if Kernel.Unicode.get () then Utf8_logic.implies else "==>")
      in
      Constraints.raise_error msg ctxt
  | Pand(lhs, rhs) ->
    let ctxt, _ = visit_quantif_relations ~is_forall ctxt lhs in
    if Constraints.has_unguarded_bounded_vars ctxt then
      visit_quantif_relations ~is_forall ctxt rhs
    else if not is_forall then
      ctxt, Some rhs
    else
      let msg =
        Format.asprintf
          "@[invalid quantification predicate, expecting '%s' to@ \
           separate the hypotheses from the goal, found '%s'@]"
          (if Kernel.Unicode.get () then Utf8_logic.implies else "==>")
          (if Kernel.Unicode.get () then Utf8_logic.conj else "&&")
      in
      Constraints.raise_error msg ctxt
  | Prel((Rlt | Rle) as r, t1, t2) ->
    let ctxt = extract_constraint ctxt t1 r t2 in
    ctxt, None
  | Prel _ ->
    Constraints.raise_error_invalid_pred ~warn_rel:true p ctxt
  | _ ->
    Constraints.raise_error_invalid_pred p ctxt

(** [compute_quantif_guards ~is_forall quantif bounded_vars p] computes the
    guards for the bounded variables [bounded_vars] of the quantification
    [quantif] from the predicate [p]. If [is_forall] is [true] then [quantif] is
    a universal quantification, otherwise [quantif] is an existential
    quantification.
    The function returns the list of guards for the variables and the goal
    predicate of the quantification. *)
let compute_quantif_guards ~is_forall quantif bounded_vars p =
  (* Traverse the predicate of the quantification to extract the guards of the
     bounded variables. *)
  let ctxt = Constraints.empty quantif bounded_vars in
  let ctxt, goal = visit_quantif_relations ~is_forall ctxt p in
  (* Check the validity of the result of the traversal. *)
  Constraints.check_validity ctxt;
  if Option.is_none goal then
    let msg =
      Format.asprintf
        "@[no goal found in quantification@ %a@]"
        Printer.pp_predicate quantif
    in
    Error.untypable msg
  else
    (* Traversal is valid, the guards and the goal can be retrieved and
       returned. *)
    let guards = Constraints.retrieve_guards ctxt in
    let goal = Option.get goal in
    guards, goal


(** Takes a guard and put it in normal form
    [t1 <= x < t2] so that [t1] is the first value
     taken by [x] and [t2] is the last one. *)
let normalize_guard ~loc (t1, rel1, lv, rel2, t2) =
  let t_plus_one t =
    let tone = Cil.lone ~loc () in
    Logic_const.term ~loc (TBinOp(PlusA, t, tone)) Linteger
  in
  (* this function only manipulate guards that were already
     processed by compute_quantif_guards, which only outputs
     guards with the constructors Rlt and Rle*)
  let t1 = match rel1 with
    | Rlt ->
      t_plus_one t1
    | Rle ->
      t1
    | Rgt | Rge | Req | Rneq ->
      assert false
  in
  let t2 = match rel2 with
    | Rlt ->
      t2
    | Rle ->
      t_plus_one t2
    | Rgt | Rge | Req | Rneq ->
      assert false
  in
  t1, lv, t2


let compute_guards loc ~is_forall p bounded_vars hyps =
  try
    let guards,goal = compute_quantif_guards p ~is_forall bounded_vars hyps in
    (* transform [guards] into [lscope_var list] *)
    let normalized_guards = List.map (normalize_guard ~loc) guards
    in Quantifier.add p (Result.Ok (normalized_guards,goal))
  with exn ->
    Quantifier.add p (Result.Error exn)

module Preprocessor : sig
  val compute : file -> unit
  val compute_annot : code_annotation -> unit
  val compute_predicate : predicate -> unit
end
= struct

  let process_quantif ~loc p =
    Cil.CurrentLoc.set loc;
    match p.pred_content with
    | Pforall(bound_vars, ({ pred_content = Pimplies(_, _) } as goal)) ->
      compute_guards loc ~is_forall:true p bound_vars goal
    | Pexists(bound_vars, ({ pred_content = Pand(_, _) } as goal)) ->
      compute_guards loc ~is_forall:false p bound_vars goal
    | Pforall _ ->
      Quantifier.add
        p
        (Result.Error (Error.make_not_yet "unguarded \\forall quantification"))
    | Pexists _ ->
      Quantifier.add
        p
        (Result.Error (Error.make_not_yet "unguarded \\exists quantification"))
    | _ -> ()

  let preprocessor = object
    inherit E_acsl_visitor.visitor dkey

    method !vannotation annot =
      match annot with
      | Dfun_or_pred _ -> Cil.DoChildren
      | _ -> Cil.SkipChildren

    method !vpredicate p =
      let loc = p.pred_loc in
      let p = Logic_normalizer.get_pred p in
      process_quantif ~loc p;
      Cil.DoChildren

  end

  let compute ast =
    preprocessor#visit_file ast

  let compute_annot annot =
    ignore @@ preprocessor#visit_code_annot annot

  let compute_predicate p =
    ignore @@ preprocessor#visit_predicate p
end

let preprocess = Preprocessor.compute
let preprocess_annot = Preprocessor.compute_annot
let preprocess_predicate = Preprocessor.compute_predicate
