let cfg_selector
    (popup_factory:GMenu.menu GMenu.factory) main_ui ~button:_ localizable = 
  match localizable with
  (* Matches global declarations that are functions. *)
  | Pretty_source.PVDecl(_, _, ({vtype = TFun(_,_,_,_)} as vi)) -> 
    let callback () = 
      let kf = Globals.Functions.get vi in
      let fundec = Kernel_function.get_definition kf in
      let window:GWindow.window = main_ui#main_window in
      Dgraph_helper.graph_window_through_dot
	~parent:window ~title:"Control flow graph"
        (dump_function fundec)
    in
    ignore (popup_factory#add_item "Show _CFG" ~callback)
  | _ -> ()

let main_gui main_ui = main_ui#register_source_selector cfg_selector

let () = Design.register_extension main_gui
