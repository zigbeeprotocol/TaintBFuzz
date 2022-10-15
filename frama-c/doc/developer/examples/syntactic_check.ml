(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2021                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*  Contact CEA LIST for licensing.                                       *)
(*                                                                        *)
(**************************************************************************)

open Cil_types
open Cil

module M = Plugin.Register

(* Each annotation in Frama-C has an emitter, for traceability.
   We create thus our own, and says that it will only be used to emit code
   annotations, and that these annotations do not depend
   on Frama-C's command line parameters.
*)
let syntax_alarm =
  Emitter.create
    "Syntactic check" [ Emitter.Code_annot ] ~correctness:[] ~tuning:[]

class non_zero_divisor prj = object (self)
  inherit Visitor.generic_frama_c_visitor (Visitor_behavior.copy prj)

  (* A division is an expression: we override the vexpr method *)
  method! vexpr e = match e.enode with
  | BinOp((Div|Mod), _, denom, _) ->
    let logic_denom = Logic_utils.expr_to_term ~coerce:false denom in
    let assertion = Logic_const.prel (Rneq, logic_denom, Cil.lzero ()) in
    (* At this point, we have built the assertion we want to insert. It remains
       to attach it to the correct statement. The cil visitor maintains the
       information of which statement and function are currently visited in
       the [current_stmt] and [current_kf] methods, which return None when
       outside of a statement or a function , e.g. when visiting a global
       declaration. Here, it necessarily returns [Some]. *)
    let stmt = match self#current_kinstr with
      | Kglobal -> assert false
      | Kstmt s -> s
    in
    let kf = Option.get self#current_kf in
    (* The above statement and function are related to the original project. We
       need to attach the new assertion to the corresponding statement and
       function of the new project. Cil provides functions to convert a
       statement (function) of the original project to the corresponding
       one of the new project. *)
    let new_stmt = Visitor_behavior.Get.stmt self#behavior stmt in
    let new_kf = Visitor_behavior.Get.kernel_function self#behavior kf in
    (* Since we are copying the file in a new project, we cannot insert
       the annotation into the current table, but in the table of the new
       project. To avoid the cost of switching projects back and forth,
       all operations on the new project are queued until the end of the
       visit, as mentioned above. This is done in the following statement. *)
    Queue.add
      (fun () ->
         Annotations.add_assert syntax_alarm ~kf:new_kf new_stmt assertion)
      self#get_filling_actions;
    DoChildren
  | _ -> DoChildren
end

(* This function creates a new project initialized with the current file plus
   the annotations related to division. *)
let create_syntactic_check_project () =
  ignore 
    (File.create_project_from_visitor "syntactic check" (new non_zero_divisor))

let () = Db.Main.extend create_syntactic_check_project
