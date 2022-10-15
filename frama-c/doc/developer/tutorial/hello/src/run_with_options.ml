let run () =
  try
  if Enabled.get() then
    let filename = Output_file.get () in
    let output msg =
      if Output_file.is_default() then
        Self.result "%s" msg
      else
        let chan = open_out filename in
        Printf.fprintf chan "%s\n" msg;
        flush chan;
        close_out chan;
    in
    output "Hello, world!"
  with Sys_error _ as exc ->
    let msg = Printexc.to_string exc in
    Printf.eprintf "There was an error: %s\n" msg
