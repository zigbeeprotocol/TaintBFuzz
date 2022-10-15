  method! vfile _ =
    Format.fprintf out "@[<hov 2>digraph cfg {@ ";
    Cil.DoChildrenPost (fun f -> Format.fprintf out "}@]@."; f)
