include Plugin.Register(
    struct
      let name = "AST diff test"
      let shortname = "AST diff test"
      let help = "Show results of AST diff computation"
    end)

let show_var vi c =
  result "Variable %a: %a"
    Cil_datatype.Varinfo.pretty vi
    Ast_diff.Varinfo.pretty_data c

let show_fun kf c =
  result "Function %a: %a"
    Kernel_function.pretty kf
    Ast_diff.Kernel_function.pretty_data c

let show_correspondances () =
  if Kernel.AstDiff.get () then begin
    result "Showing correspondances between %s and %s"
      (Project.get_name (Ast_diff.Orig_project.get()))
      (Project.get_name (Project.current()));
    Ast_diff.Varinfo.iter show_var;
    Ast_diff.Kernel_function.iter show_fun;
  end

let () = Db.Main.extend show_correspondances
