module Output_file = Self.String
  (struct
    let option_name = "-hello-output"
    let default = "-"
    let arg_name = "output-file"
    let help =
      "file where the message is output (default: output to the console)"
   end)
