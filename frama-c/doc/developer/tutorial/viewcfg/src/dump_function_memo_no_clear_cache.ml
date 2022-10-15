let dump_function fundec fmt =
  Format.fprintf fmt "@[digraph cfg {%s}@]@\n" 
    (dump_to_string_memoized fundec)
