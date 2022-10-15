let dump_to_string fundec = 
  Self.feedback "Computing CFG for function %s" (fundec.svar.vorig_name);
  ignore 
    (Visitor.visitFramacFunction (new print_cfg Format.str_formatter) fundec);
  Format.flush_str_formatter ()

let dump_to_string_memoized = Cfg_graph_state.memo dump_to_string
