open Cil_types

class print =
  object
    inherit Visitor.frama_c_inplace

    method! vglob_aux g =
      begin match g with
      | GFun(fd, _) ->
        Kernel.feedback "%a is%s ghost"
          Cil_datatype.Varinfo.pretty fd.svar
          (if fd.svar.vghost then "" else " not")
      | GFunDecl(_, vi, _) ->
        Kernel.feedback "%a is%s ghost"
          Cil_datatype.Varinfo.pretty vi
          (if vi.vghost then "" else " not")
      | _ -> ()
      end ;
      Cil.DoChildren

    method! vstmt_aux s =
      Kernel.feedback "%a is a%s ghost statement"
        Cil_datatype.Stmt.pretty s
        (if s.ghost then "" else " non")
      ;
      Cil.DoChildren

    method! vvdec vi =
      Kernel.feedback "%a is a%s ghost %s"
        Cil_datatype.Varinfo.pretty vi
        (if vi.vghost then "" else " non")
        (if vi.vformal then "formal"
         else if vi.vglob then "global"
         else "local") ;
      Cil.DoChildren
  end

let run () = Visitor.visitFramacFileSameGlobals (new print) (Ast.get())

let () = Db.Main.extend run
