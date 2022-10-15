let dump_function fundec fmt =
  if not (Value_is_computed.get ()) && Eva.Analysis.is_computed () then begin 
    Value_is_computed.set true;
    let selection = State_selection.with_dependencies Cfg_graph_state.self in
    Project.clear ~selection ();
  end;
  Format.fprintf fmt "@[digraph cfg {%s}@]@." (dump_to_string_memoized fundec)
