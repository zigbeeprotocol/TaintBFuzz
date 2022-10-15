let run () =
  List.iter (fun (pos1, pos2, fname) ->
      Format.printf "%a - %a -> %s@."
        Cil_datatype.Position.pp_with_col pos1
        Cil_datatype.Position.pp_with_col pos2
        fname
    ) (Cabs2cil.func_locs ())

let () = Db.Main.extend run
