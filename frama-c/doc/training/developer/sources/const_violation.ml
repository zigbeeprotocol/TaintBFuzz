let run () =
  let () = Ast.compute () in
  let glob = Globals.Vars.find_from_astinfo "Glob" Cil_types.VGlobal in
  let glob_expr = Cil.evar ~loc:Cil_datatype.Location.unknown glob in
  let main = Globals.Functions.find_by_name "main" in
  let () = Eva.Analysis.compute () in
  let init_stmt = Kernel_function.find_first_stmt main in
  let init_state = Db.Value.get_stmt_state init_stmt in
  let end_stmt = Kernel_function.find_return main in
  let end_state = Db.Value.get_stmt_state end_stmt in
  let init_binding = !Db.Value.eval_expr init_state glob_expr in
  let end_binding = !Db.Value.eval_expr end_state glob_expr in
  let init_val = Cvalue.V.project_ival init_binding in
  let end_val = Cvalue.V.project_ival end_binding in
  if Ival.is_singleton_int init_val && Ival.is_singleton_int end_val then begin
    if not
      (Abstract_interp.Int.equal
         (Ival.project_int init_val) (Ival.project_int end_val))
    then
      Kernel.error "Glob has been assigned"
  end else begin
    Kernel.warning "Imprecise value for Glob";
    if Ival.intersects init_val end_val then
      Kernel.warning "Glob might have been assigned"
    else
      Kernel.error "Glob has been assigned"
  end

let () = Db.Main.extend run
