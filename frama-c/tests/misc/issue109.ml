let main () =
  Eva.Analysis.compute ();
  Dynamic.Parameter.String.set "" "";
  Dynamic.Parameter.String.set "" "issue109.i";
  File.init_from_cmdline ();
  Eva.Analysis.compute ()

let main = Db.Main.extend main
