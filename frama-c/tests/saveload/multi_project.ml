let check name test =
  Kernel.log "Checking %S@." name;
  Project.on
    (Project.from_unique_name name)
    (fun () -> assert (test (Kernel.Files.get ()) [])) ()

let main () =
  ignore (Project.create_by_copy ~last:false "foo");
  ignore (Project.create "foobar");
  let fp = Filepath.Normalized.of_string "foo.sav" in
  Project.save_all fp;
  check "foo" (<>);
  check "foobar" (=);
  check "default" (<>);
  Kernel.Files.set [];
  Project.load_all fp;
  Extlib.safe_remove "foo.sav";
  ignore (Project.create_by_copy ~last:false "bar");
  assert
    (Project.equal (Project.current ()) (Project.from_unique_name "default"));
  check "foo" (<>);
  check "foobar" (=);
  check "default" (<>);
  check "bar" (<>)

let () = Db.Main.extend main
