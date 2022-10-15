let output msg =
  try
    let filename = Hello_options.Output_file.get () in
    if Hello_options.Output_file.is_default () then
      Hello_options.Self.result "%s" msg
    else
      let chan = open_out filename in
      Printf.fprintf chan "%s\n" msg;
      flush chan;
      close_out chan
  with Sys_error _ as exc ->
    let msg = Printexc.to_string exc in
    Printf.eprintf "There was an error: %s\n" msg
