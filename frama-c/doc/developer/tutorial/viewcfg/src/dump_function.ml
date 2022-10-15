let dump_function fundec fmt = 
  Format.fprintf fmt "@[<hov 2>digraph cfg {@ ";
  ignore(Visitor.visitFramacFunction (new print_cfg fmt) fundec);
  Format.fprintf fmt "}@]@\n"
