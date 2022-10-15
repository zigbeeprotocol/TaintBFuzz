

(* Run the user commands *)
let run () =
  let p_default =
    Project.create_by_copy
      ~src:(Project.from_unique_name "default")
      ~last:false
      "default"
  in
  Eva.Analysis.compute ();
  Project.set_current p_default;
  Eva.Analysis.compute ();
  ()

let () = Db.Main.extend run 
