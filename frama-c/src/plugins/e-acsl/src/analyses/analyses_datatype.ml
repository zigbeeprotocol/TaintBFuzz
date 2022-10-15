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

(** Datatypes for analyses types *)

open Cil_types
open Cil_datatype
open Analyses_types

module Annotation_kind =
  Datatype.Make
    (struct
      type t = annotation_kind
      let name = "E_ACSL.Annotation_kind"
      let reprs = [ Assertion ]
      include Datatype.Undefined

      let pretty fmt akind =
        match akind with
        | Assertion -> Format.fprintf fmt "Assertion"
        | Precondition -> Format.fprintf fmt "Precondition"
        | Postcondition -> Format.fprintf fmt "Postcondition"
        | Invariant -> Format.fprintf fmt "Invariant"
        | Variant -> Format.fprintf fmt "Variant"
        | RTE -> Format.fprintf fmt "RTE"
    end)

module Pred_or_term =
  Datatype.Make_with_collections
    (struct
      type t = pred_or_term

      let name = "E_ACSL.Pred_or_term"

      let reprs =
        let reprs =
          List.fold_left
            (fun reprs t -> PoT_term t :: reprs)
            []
            Term.reprs
        in
        List.fold_left
          (fun reprs p -> PoT_pred p :: reprs)
          reprs
          Predicate.reprs

      include Datatype.Undefined

      let compare pot1 pot2 =
        match pot1, pot2 with
        | PoT_pred _, PoT_term _ -> -1
        | PoT_term _, PoT_pred _ -> 1
        | PoT_pred p1, PoT_pred p2 -> PredicateStructEq.compare p1 p2
        | PoT_term t1, PoT_term t2 -> Term.compare t1 t2

      let equal = Datatype.from_compare

      let hash = function
        | PoT_pred p -> 7 * PredicateStructEq.hash p
        | PoT_term t -> 97 * Term.hash t

      let pretty fmt = function
        | PoT_pred p -> Printer.pp_predicate fmt p
        | PoT_term t -> Printer.pp_term fmt t

      let varname _ = "pred_or_term"
    end)

(** [Ext_logic_label] associates a statement to a label when necessary. For
    instance, the label `Old` is associated with its contract statement to
    distinguish two `Old` annotations in the same function. On the contrary, the
    `Pre` label does not have an associated statement because this label
    represents the same location for all contracts in the same function. *)
module Ext_logic_label: sig
  include Datatype.S_with_collections with type t = logic_label * stmt option

  val get: kinstr -> logic_label -> logic_label * stmt option
  (** @return an extended logic label from a [kinstr] and a [logic_label]. *)

end = struct

  include Datatype.Pair_with_collections
      (Logic_label)
      (Datatype.Option_with_collections
         (Stmt)
         (struct
           let module_name = "E_ACSL.Labels.Ext_logic_label.StmtOption"
         end))
      (struct let module_name = "E_ACSL.Labels.Ext_logic_label" end)

  (* Override [pretty] to print a more compact representation of
     [Ext_logic_label] for debugging purposes. *)
  let pretty fmt (label, from_stmt_opt) =
    match from_stmt_opt with
    | Some from_stmt ->
      Format.fprintf fmt "%a from stmt %d at %a"
        Logic_label.pretty label
        from_stmt.sid
        Printer.pp_location (Stmt.loc from_stmt)
    | None ->
      Format.fprintf fmt "%a"
        Logic_label.pretty label

  let get kinstr label =
    let from_stmt_opt =
      match kinstr, label with
      | Kglobal, _
      | Kstmt _, (BuiltinLabel (Pre | Here | Init)
                 | FormalLabel _ | StmtLabel _) ->
        None
      | Kstmt _, BuiltinLabel (LoopCurrent | LoopEntry) ->
        (* [None] for now because these labels are unsupported, but the
           statement before the loop and the first statement of the loop should
           probably be used once they are supported. *)
        Error.print_not_yet
          (Format.asprintf "label %a" Printer.pp_logic_label label);
        None
      | Kstmt s, BuiltinLabel (Old | Post) -> Some s
    in
    label, from_stmt_opt

end

(** Basic printer for a [kinstr]. Contrary to [Cil_datatype.Kinstr.pretty], the
    stmt of [Kstmt] is not printed. *)
let basic_pp_kinstr fmt kinstr =
  Format.fprintf fmt "%s"
    (match kinstr with
     | Kglobal -> "Kglobal"
     | Kstmt _ -> "Kstmt")

(** Basic comparison for two [kinstr], i.e. two [Kstmt] are always equal
    regardless of the statement value (contrary to [Cil_datatype.Kinstr.compare]
    where two [Kstmt] are compared with their included statement's [sid]). *)
let basic_kinstr_compare kinstr1 kinstr2 =
  match kinstr1, kinstr2 with
  | Kglobal, Kglobal | Kstmt _, Kstmt _ -> 0
  | Kglobal, _ -> 1
  | _, Kglobal -> -1

(** Basic hash function for a [kinstr], i.e. contrary to
    [Cil_datatype.Kinstr.hash] the statement of the [Kstmt] is not considered
    for the hash. *)
let basic_kinstr_hash kinstr =
  match kinstr with
  | Kglobal -> 1 lsl 29
  | Kstmt _ -> 1 lsl 31

module At_data = struct
  let create ?error kf kinstr lscope pot label =
    { kf; kinstr; lscope; pot; label; error }

  include Datatype.Make_with_collections
      (struct
        type t = at_data
        let name = "E_ACSL.At_data"

        let reprs =
          List.fold_left
            (fun acc kf ->
               List.fold_left
                 (fun acc kinstr ->
                    List.fold_left
                      (fun acc pot ->
                         List.fold_left
                           (fun acc label ->
                              create kf kinstr Lscope.empty pot label :: acc)
                           acc
                           Logic_label.reprs)
                      acc
                      Pred_or_term.reprs)
                 acc
                 Kinstr.reprs)
            []
            Kf.reprs

        include Datatype.Undefined

        let compare
            { kf = kf1;
              kinstr = kinstr1;
              lscope = lscope1;
              pot = pot1;
              label = label1 }
            { kf = kf2;
              kinstr = kinstr2;
              lscope = lscope2;
              pot = pot2;
              label = label2 }
          =
          let cmp = Kf.compare kf1 kf2 in
          let cmp =
            if cmp = 0 then
              basic_kinstr_compare kinstr1 kinstr2
            else cmp
          in
          let cmp =
            if cmp = 0 then Lscope.D.compare lscope1 lscope2
            else cmp
          in
          let cmp =
            if cmp = 0 then Pred_or_term.compare pot1 pot2
            else cmp
          in
          if cmp = 0 then
            let elabel1 = Ext_logic_label.get kinstr1 label1 in
            let elabel2 = Ext_logic_label.get kinstr2 label2 in
            Ext_logic_label.compare elabel1 elabel2
          else cmp

        let equal = Datatype.from_compare

        let hash { kf; kinstr; lscope; pot; label } =
          let elabel = Ext_logic_label.get kinstr label in
          Hashtbl.hash
            (Kf.hash kf,
             basic_kinstr_hash kinstr,
             Lscope.D.hash lscope,
             Pred_or_term.hash pot,
             Ext_logic_label.hash elabel)

        let pretty fmt { kf; kinstr; lscope; pot; label } =
          let elabel = Ext_logic_label.get kinstr label in
          Format.fprintf fmt "@[(%a, %a, %a, %a, %a)@]"
            Kf.pretty kf
            basic_pp_kinstr kinstr
            Lscope.D.pretty lscope
            Pred_or_term.pretty pot
            Ext_logic_label.pretty elabel
      end)
end
