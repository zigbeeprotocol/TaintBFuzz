open Cil_types

let e = Emitter.(create "test" [ Code_annot ] ~correctness:[] ~tuning:[])

let run () =
  Ast.compute();
  let vis = object(self)
    inherit Visitor.frama_c_inplace
    method! vinst =
      function
      | Call(_,{enode=Lval(Var f,NoOffset)},[arg],_)
        when f.vname = "__FC_assert" ->
        let p = Logic_utils.expr_to_predicate arg in
        Annotations.add_assert e (Option.get self#current_stmt) p;
        Cil.SkipChildren
      | _ -> Cil.SkipChildren
  end
  in
  Visitor.visitFramacFileSameGlobals vis (Ast.get());
  Filecheck.check_ast "Test"

let () = Db.Main.extend run
