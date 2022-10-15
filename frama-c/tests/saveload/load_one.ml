let sav_file = "load_one.sav"

let () = at_exit (fun _ -> Sys.remove sav_file)

let main () =
  let sparecode () =
    Sparecode.Register.get ~select_annot:false ~select_slice_pragma:false
  in
  let fp = Filepath.Normalized.of_string sav_file in
  let p = sparecode () in
  Project.save fp;
  Project.remove ~project:p ();
  let p = Project.load fp in
  Project.on p (fun () -> Eva.Analysis.compute (); ignore (sparecode ())) ()

let () = Db.Main.extend main

(* testing Project.create_by_copy *)
let main2 () =
  Eva.Analysis.compute ();
  let prj = Project.create_by_copy ~last:false "copy" in
  Format.printf "INIT AST@.";
  File.pretty_ast ();
  Format.printf "COPY AST@.";
  File.pretty_ast ~prj ()

let () = Db.Main.extend main2
