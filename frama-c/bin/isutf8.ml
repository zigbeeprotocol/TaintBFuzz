module StringSet = Set.Make(String)

exception False

let is_valid_utf8 filename =
  let buf = Bytes.create 1024 in
  try
    let ic = open_in_bin filename in
    let extra = ref 0 in
    try
      while true do
        let n_bytes_read = input ic buf 0 1024 in
        if n_bytes_read = 0 then raise End_of_file;
        for i = 0 to n_bytes_read - 1 do
          let c = Bytes.get_uint8 buf i in
          (*Format.printf "extra: %d, read byte: %d (0x%x, char %c)@."
            !extra c c (Char.chr c);*)
          if !extra > 0 then begin
            decr extra;
            if c lsr 6 <> 2 then raise False
          end
          else
          if c > 127 then begin
            if c lsr 5 = 6 then extra := 1
            else if c lsr 4 = 14 then extra := 2
            else if c lsr 3 = 30 then extra := 3
            else raise False
          end;
        done;
      done;
      close_in ic;
      !extra = 0
    with
    | End_of_file ->
      close_in ic;
      !extra = 0
    | False ->
      close_in ic;
      false
  with
  | Sys_error msg ->
    (* possibly a non-existing file (e.g. with spaces); ignoring *)
    Format.printf "isutf8: cannot open, ignoring file: %s (%s)@."
      filename msg;
    true

(* usage: first argument is a file name containing a list of files
   (one per line) to be checked; the remaining arguments are filenames
   to be ignored during checking. *)
let () =
  if Array.length Sys.argv < 2 then begin
    Format.printf "usage: %s file_list.txt [ignore1 ignore2 ...]@." Sys.argv.(0);
    exit 0
  end;
  let errors = ref 0 in
  let file_list_ic = open_in Sys.argv.(1) in
  let to_ignore = StringSet.of_list (List.tl (Array.to_list Sys.argv)) in
  begin
    try
      while true; do
        let filename = input_line file_list_ic in
        if not (StringSet.mem filename to_ignore)
        && not (is_valid_utf8 filename) then begin
          incr errors;
          Format.printf "error: invalid UTF-8 in file: %s@." filename
        end
      done
    with End_of_file ->
      close_in file_list_ic
  end;
  if !errors > 0 then begin
    Format.printf "Found %d file(s) with errors.@." !errors;
    exit 1
  end else
    exit 0
