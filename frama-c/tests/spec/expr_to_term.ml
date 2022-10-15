open Cil_types

let emitter = Emitter.(create "Test" [Funspec] ~correctness:[] ~tuning:[])

let check_expr_term check fct s post =
  let exp =
    match s.skind with
      | Instr (Set (lv,_,loc)) -> Cil.new_exp ~loc (Lval lv)
      | If (c,_,_,_) -> c
      | _ -> Kernel.fatal "Unexpected statement %a" Printer.pp_stmt s
  in
  let term =
    match post with
      | (_,{ip_content={tp_statement={pred_content = Papp(_,_,[l;_])}}}) -> l
      | _ -> Kernel.fatal "Unexpected ensures %a" Printer.pp_post_cond post
  in
  let term' = Logic_utils.expr_to_term ~coerce:false exp in
  if check && not (Cil_datatype.Term.equal term term') then
    Kernel.fatal
      "translation of C expression %a is %a, inconsistent with logic term %a"
      Printer.pp_exp exp Printer.pp_term term' Printer.pp_term term;
  let p = List.hd (Logic_env.find_all_logic_functions "int_eq") in
  let app = Logic_const.papp (p,[],[term;term']) in
  let post = Logic_const.new_predicate app in
  Annotations.add_ensures emitter fct [Normal,post]

let check_expr_pred fct s post =
  let exp =
    match s.skind with
    | Instr (Call(_,_,[x],_)) -> x
    | _ -> Kernel.fatal "Unexpected statement %a" Printer.pp_stmt s
  in
  let pred = (snd post).ip_content.tp_statement in
  let pred' = Logic_utils.expr_to_predicate exp in
  if not (Logic_utils.is_same_predicate pred pred') then
    Kernel.fatal
      "translation of C expression %a is %a, inconsistent with predicate %a"
      Printer.pp_exp exp Printer.pp_predicate pred' Printer.pp_predicate pred;
  let post = Logic_const.new_predicate pred' in
  Annotations.add_ensures emitter fct [Normal,post]

let treat_fct check fct =
  let stmts = (Kernel_function.get_definition fct).sbody.bstmts in
  let stmts =
    List.filter
      (function
        { skind = Instr (Set (lv,_,_)) } ->
          (match lv with (Var v,_) -> v.vglob | _ -> true)
        | { skind = If _ } -> true
        | _ -> false)
      stmts
  in
  let ensures = (List.hd (Annotations.funspec fct).spec_behavior).b_post_cond
  in
  (* A bit fragile, but should do the trick as long as the test itself does
     not get too complicated (regarding the C code at least). *)
  if not (List.length stmts = List.length ensures) then
    Kernel.fatal
      "Stmts:@\n%a@\nPreds:@\n%a@\n"
      (Pretty_utils.pp_list ~sep:"@\n@\n" Printer.pp_stmt) stmts
      (Pretty_utils.pp_list ~sep:"@\n@\n" Printer.pp_post_cond) ensures;
  List.iter2 (check_expr_term check fct) stmts ensures;
  Filecheck.check_ast "check_expr_to_term"

let treat_fct_pred fct =
  let stmts = (Kernel_function.get_definition fct).sbody.bstmts in
  let stmts =
    List.filter
      (fun x -> match x.skind with Instr(Call _) -> true | _ -> false)
      stmts
  in
  let ensures = (List.hd (Annotations.funspec fct).spec_behavior).b_post_cond in
  if List.length stmts <> List.length ensures then
    Kernel.fatal "ill-formed test in function %a" Kernel_function.pretty fct;
  List.iter2 (check_expr_pred fct) stmts ensures;
  Filecheck.check_ast "check_expr_to_predicate"

let compute () =
  let main = Globals.Functions.find_by_name "main" in
  let f = Globals.Functions.find_by_name "f" in
  let g = Globals.Functions.find_by_name "g" in
  let h = Globals.Functions.find_by_name "h" in
  let i = Globals.Functions.find_by_name "i" in
  begin
    treat_fct true main;
    treat_fct false f;
    treat_fct true g;
    treat_fct true h;
    treat_fct_pred i;
  end

let () = Db.Main.extend compute
