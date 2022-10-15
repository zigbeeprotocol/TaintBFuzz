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

let pred_opt_from_expr_state stmt e =
  try
    Value2acsl.lval_to_predicate stmt e
  with
  | Cvalue.V.Not_based_on_null ->
    Misc.not_implemented ~what:"Value not based on null";
    None
  | Misc.Not_implemented what ->
    Misc.not_implemented ~what;
    None

class hypotheses_visitor (env: Collect.env) = object(self)
  inherit Visitor.generic_frama_c_visitor (Visitor_behavior.inplace ())

  method! vstmt_aux stmt =
    let kf = Option.get (self#current_kf) in
    if Collect.should_annotate_stmt env stmt then begin
      let vars = Collect.get_relevant_vars_stmt env kf stmt in
      List.iter
        (fun e ->
           let p_opt = pred_opt_from_expr_state stmt e in
           Option.iter (Misc.assert_and_validate ~kf stmt) p_opt)
        vars
    end;
    Cil.DoChildren
end


let generate_hypotheses env =
  let visitor = new hypotheses_visitor env in
  Cil.visitCilFileSameGlobals (visitor :> Cil.cilVisitor) (Ast.get ())
