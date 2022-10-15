module Cfg_graph_state = State_builder.Hashtbl
  (Cil_datatype.Fundec.Hashtbl)
  (Datatype.String)
  (struct
    let name = "Data_for_cfg.Cfg_graph_state"
    let dependencies = [ Ast.self; Db.Value.self ]
    let size = 17
   end);;
