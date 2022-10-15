let foo () =
  if Project.get_name (Project.current ()) <> "prj" then begin
    let prj = Project.create "prj" in
    let () = Project.set_current prj in
    let f = Filepath.Normalized.of_string "big_local_array.i" in
    File.init_from_c_files [File.from_filename f]
  end

let () = Db.Main.extend foo
