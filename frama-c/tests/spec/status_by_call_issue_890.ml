let () =
  Db.Main.extend
    (fun () -> Globals.Functions.iter Statuses_by_call.setup_all_preconditions_proxies)
