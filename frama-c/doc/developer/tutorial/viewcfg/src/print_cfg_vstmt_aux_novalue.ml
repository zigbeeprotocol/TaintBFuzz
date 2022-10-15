  method! vstmt_aux s =
    Format.fprintf out "@[<hov 2>s%d@ [label=%S]@];@ "
      s.sid (Pretty_utils.to_string print_stmt s.skind);
    List.iter 
      (fun succ -> Format.fprintf out "@[s%d -> s%d;@]@ " s.sid succ.sid)
      s.succs;
    Format.fprintf out "@]";
    Cil.DoChildren
