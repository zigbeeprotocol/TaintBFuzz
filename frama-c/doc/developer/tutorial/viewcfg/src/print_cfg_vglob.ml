  method! vglob_aux g =
    match g with
    | GFun(f,_) ->
        Format.fprintf out "@[<hov 2>subgraph cluster_%a {@ \
                           @[<hv 2>graph@ [label=\"%a\"];@]@ " 
          Printer.pp_varinfo f.svar
          Printer.pp_varinfo f.svar;
        Cil.DoChildrenPost(fun g -> Format.fprintf out "}@]@ "; g)
    | _ -> Cil.SkipChildren
