let () =
  Db.Main.extend (fun _ ->
      ignore (Sparecode.Register.get ~select_annot:true
                ~select_slice_pragma:true))
