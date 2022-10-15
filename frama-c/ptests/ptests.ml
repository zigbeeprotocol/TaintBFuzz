(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  you can redistribute it and/or modify it under the terms of the GNU   *)
(*  Lesser General Public License as published by the Free Software       *)
(*  Foundation, version 2.1.                                              *)
(*                                                                        *)
(*  It is distributed in the hope that it will be useful,                 *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         *)
(*  GNU Lesser General Public License for more details.                   *)
(*                                                                        *)
(*  See the GNU Lesser General Public License version 2.1                 *)
(*  for more details (enclosed in the file licenses/LGPLv2.1).            *)
(*                                                                        *)
(**************************************************************************)

let system =
  if Sys.os_type = "Win32" then
    fun f ->
      Unix.system (Format.sprintf "bash -c %S" f)
  else
    fun f ->
      Unix.system f

module Filename = struct
  include Filename
  let concat =
    if Sys.os_type = "Win32" then
      fun a b -> a ^ "/" ^ b
    else
      concat

  let cygpath r =
    let cmd =
      Format.sprintf
        "bash -c \"cygpath -m %s\""
        (String.escaped (String.escaped r))
    in
    let in_channel  = Unix.open_process_in cmd in
    let result = input_line in_channel in
    ignore(Unix.close_process_in in_channel);
    result

  let temp_file =
    if Sys.os_type = "Win32" then
      fun a b -> let r = temp_file a b in
        cygpath r
    else
      fun a b -> temp_file a b

  let sanitize f = String.escaped f
end

let string_del_suffix suffix s =
  let lsuffix = String.length suffix in
  let ls = String.length s in
  if ls >= lsuffix && String.sub s (ls - lsuffix) lsuffix = suffix then
    Some (String.sub s 0 (ls - lsuffix))
  else None

let str_mutex = Mutex.create()

let str_global_replace regex repl s =
  Mutex.lock str_mutex;
  let res = Str.global_replace regex repl s in
  Mutex.unlock str_mutex; res

(* The match may start after [pos] (instead of [str_string_match]) *)
let str_string_contains regexp s pos =
  Mutex.lock str_mutex;
  let res = try
      ignore (Str.search_forward regexp s pos) ;
      true
    with Not_found -> false
  in
  Mutex.unlock str_mutex; res

let str_string_contains_option opt =
  let re = Str.regexp ("\\( \\|^\\)"^ opt ^ "\\( \\|=\\|$\\)") in
  str_string_contains re

let str_string_match regex s n =
  Mutex.lock str_mutex;
  let res = Str.string_match regex s n in
  Mutex.unlock str_mutex; res

let str_string_match1 regexp line pos =
  Mutex.lock str_mutex;
  let res = if Str.string_match regexp line pos then
      try
        Some (Str.matched_group 1 line)
      with Not_found -> None
    else None
  in
  Mutex.unlock str_mutex; res

let str_string_match2 regexp line pos =
  Mutex.lock str_mutex;
  let res = if Str.string_match regexp line pos then
      try
        Some ((Str.matched_group 1 line), (Str.matched_group 2 line))
      with Not_found -> None
    else None
  in
  Mutex.unlock str_mutex; res

(* If regex1 matches inside s, adds suffix to the first occurrence of regex2.
   If matched, returns (replaced string, true), otherwise returns (s, false).
*)
let str_string_match_and_replace regex1 regex2 ~suffix s =
  Mutex.lock str_mutex;
  let replaced_str, matched =
    if Str.string_match regex1 s 0 then
      Str.replace_first regex2 ("\\1" ^ suffix) s, true
    else s, false
  in
  Mutex.unlock str_mutex;
  (replaced_str, matched)

let str_bounded_full_split regex s n =
  Mutex.lock str_mutex;
  let res = Str.bounded_full_split regex s n in
  Mutex.unlock str_mutex; res

let str_split regex s =
  Mutex.lock str_mutex;
  let res = Str.split regex s in
  Mutex.unlock str_mutex; res

let str_split_list =
  (* considers blanks (not preceded by '\'), tabs and commas as separators *)
  let nonsep_regexp = Str.regexp "[\\] " in (* removed for beeing reintroduced *)
  let sep_regexp = Str.regexp "[\t ,]+" in
  fun s -> (* splits on '\ ' first then on ' ' or ',' *)
    Mutex.lock str_mutex;
    let r = List.fold_left (fun acc -> function
        | Str.Text s -> List.rev_append (Str.full_split sep_regexp s) acc
        | (Str.Delim _ as delim) -> delim::acc)
        []
        (Str.full_split nonsep_regexp s)
    in (* [r] is in the reverse order and the next [fold] restores the order *)
    Mutex.unlock str_mutex;
    let add s (glue,prev,curr) =
      if glue then false,(s^prev),curr
      else false,s,(if prev = "" then curr else prev::curr)
    in
    let acc = List.fold_left (fun ((_,prev,curr) as acc) -> function
        | Str.Delim ("\\ " as nonsep) ->
          true,(nonsep^prev),curr (* restore '\ ' *)
        | Str.Delim _ -> add "" acc (* separator *)
        | Str.Text s -> add s acc) (false,"",[]) r
    in
    let _,_,res = (add "" acc) in
    res

(* removes first blanks *)
let trim_right s =
  if s = "" then s else begin
    let n = ref (String.length s - 1) in
    let last_char_to_keep =
      try
        while !n > 0 do
          if String.get s !n <> ' ' then raise Exit;
          n := !n - 1
        done;
        0
      with Exit -> !n
    in
    String.sub s 0 (last_char_to_keep+1)
  end

let default_env = ref []

let add_default_env x y = default_env:=(x,y)::!default_env

let add_env var value =
  add_default_env var value;
  Unix.putenv var value

let print_default_env fmt =
  match !default_env with
    [] -> ()
  | l ->
    Format.fprintf fmt "@[Env:@\n";
    List.iter (fun (x,y) -> Format.fprintf fmt "%s = \"%s\"@\n"  x y) l;
    Format.fprintf fmt "@]"

let get_default_env var value =
  try
    let v = Unix.getenv var in
    add_default_env (var ^ " (set from outside)") v;
    v
  with Not_found -> add_env var value ; value

let default_env var value = ignore (get_default_env var value)

let get_default_env_of_int var value =
  try
    int_of_string (get_default_env var (string_of_int value))
  with _ -> value

(* 0 -> no change
   1 -> apply a filter (about pathname) to prepare oracles
   2 -> run tests from result directories (except make command)
*)
let dune_mode = ref (get_default_env_of_int "PTEST_DUNE_MODE" 2)

(** the name of the directory-wide configuration file*)
let dir_config_file = "test_config"

(** the files in [suites] whose name matches
    the pattern [test_file_regexp] will be considered as test files *)
let test_file_regexp = ".*\\.\\(c\\|i\\)$"

(* Splits the command string to separate the command name from the parameters
   [let cmd_name,param=command_partition cmd in assert cmd=cmd_name^param]
*)
let command_partition =
  let regexp_unescaped_blank = Str.regexp "[^\\ ] " in
  fun cmd ->
    match str_bounded_full_split regexp_unescaped_blank cmd 2 with
    | [ Str.Text cmd ] ->
      cmd, ""
    | [ Str.Text cmd ; Str.Delim delim ] ->
      cmd ^ (String.make 1 (String.get delim 0)), (String.make 1 (String.get delim 1))
    | [ Str.Text cmd ; Str.Delim delim; Str.Text options ] ->
      cmd ^ (String.make 1 (String.get delim 0)), (String.make 1 (String.get delim 1)) ^ options
    | [ Str.Delim delim ] ->
      (String.make 1 (String.get delim 0)), (String.make 1 (String.get delim 1))
    | [ Str.Delim delim; Str.Text options ] ->
      (String.make 1 (String.get delim 0)), (String.make 1 (String.get delim 1)) ^ options
    | _ -> assert false

let opt_to_byte_options =
  let regex_cmxs = Str.regexp ("\\([^/]+\\)[.]cmxs\\($\\|[ \t]\\)") in
  fun options -> str_global_replace regex_cmxs "\\1.cmo\\2" options

let output_unix_error (exn : exn) =
  match exn with
  | Unix.Unix_error (error, _function, arg) ->
    let message = Unix.error_message error in
    if arg = "" then
      Format.eprintf "%s@." message
    else
      Format.eprintf "%s: %s@." arg message
  | _ -> assert false

let mv src dest =
  try
    Unix.rename src dest
  with Unix.Unix_error _ as e ->
    output_unix_error e

let unlink ?(silent = true) file =
  let open Unix in
  try
    Unix.unlink file
  with
  | Unix_error _ when silent -> ()
  | Unix_error (ENOENT,_,_) -> () (* Ignore "No such file or directory" *)
  | Unix_error _ as e -> output_unix_error e

let fail s =
  Format.printf "Error: %s@." s;
  exit 2

let is_nonexisting_link filename =
  let open Unix in
  try
    match (lstat filename).st_kind with
    | S_LNK -> false
    | _ -> fail ("Existing result file with the same name than one in the upper directory:" ^ filename)
  with
  | Unix_error (UnixLabels.ENOENT, _, _) -> (* file does not exist *)
    true
  | Unix_error _ as e ->
    output_unix_error e;
    raise e

let is_nonexisting_file filename =
  let open Unix in
  try
    match (lstat filename).st_kind with
    | S_REG -> false
    | _ -> fail ("Existing result file with the same name than one in the upper directory:" ^ filename)
  with
  | Unix_error (UnixLabels.ENOENT, _, _) -> (* file does not exist *)
    true
  | Unix_error _ as e ->
    output_unix_error e;
    raise e

let is_file_empty_or_nonexisting filename =
  let open Unix in
  try
    (Unix.stat filename).st_size = 0
  with
  | Unix_error (UnixLabels.ENOENT, _, _) -> (* file does not exist *)
    true
  | Unix_error _ as e ->
    output_unix_error e;
    raise e

let base_path = Filename.current_dir_name
(*    (Filename.concat
        (Filename.dirname Sys.executable_name)
        Filename.parent_dir_name)
*)

(** Command-line flags *)

type behavior = Examine | Update | Run | Show | Gui
let behavior = ref (if 1 = (get_default_env_of_int "PTEST_UPDATE" 0)
                    then Update else Run)

let verbosity = ref 0
let dry_run = ref false
let use_byte = ref false
let use_diff_as_cmp = ref (Sys.os_type = "Win32")
let do_diffs = ref (if Sys.os_type = "Win32" then "diff --strip-trailing-cr -u"
                    else "diff -u")
let do_cmp = ref (if Sys.os_type="Win32" then !do_diffs
                  else "cmp -s")
let do_make = ref "make"
let n = ref 4    (* the level of parallelism *)

(** special configuration, with associated oracles *)
let special_config = ref (get_default_env "PTEST_CONFIG" "")
let do_error_code = ref false

let xunit = ref false

let io_mutex = Mutex.create ()

let lock_fprintf f =
  Mutex.lock io_mutex;
  Format.kfprintf (fun _ -> Mutex.unlock io_mutex) f

let lock_printf s = lock_fprintf Format.std_formatter s
let lock_eprintf s = lock_fprintf Format.err_formatter s

let suites = ref []
let make_test_suite s =
  suites := s :: !suites

let exclude_suites = ref []
let exclude s = exclude_suites := s :: !exclude_suites

let macro_post_options = ref "" (* value set to @PTEST_POST_OPTIONS@ macro *)
let macro_pre_options  = ref "" (* value set to @PTEST_PRE_OPTIONS@  macro *)
let macro_options = ref "@PTEST_PRE_OPTIONS@ @PTEST_OPT@ @PTEST_POST_OPTIONS@"
let macro_default_options = ref "-journal-disable -check -no-autoload-plugins"

let macro_frama_c_cmd = ref "@frama-c-exe@ @PTEST_DEFAULT_OPTIONS@"
let macro_frama_c     = ref "@frama-c-exe@ @PTEST_DEFAULT_OPTIONS@ @PTEST_LOAD_OPTIONS@"
let default_toplevel = ref "@frama-c@"

(* Those variables are read from a ptests_config file *)
let toplevel_path = ref "" (* value set to @frama-c-exe@ macro *)
let default_suites = ref []

let () =
  Unix.putenv "LC_ALL" "C" (* for oracles that depend on the locale *)

let example_msg =
  Format.sprintf
    "@.@[<v 0>\
     A test suite can be the name of a directory in ./tests or \
     the path to a file.@ @ \
     Directives of \"test_config[_<mode>]\" files:@  \
     COMMENT: <comment>   @[<v 0># Just a comment line.@]@  \
     FILEREG: <regexp>    @[<v 0># Ignores the files in suites whose name doesn't matche the pattern.@]@  \
     DONTRUN:             @[<v 0># Ignores the file.@]@  \
     EXECNOW: ([LOG|BIN] <file>)+ <command>  @[<v 0># Defines the command to execute to build a 'LOG' (textual) 'BIN' (binary) targets.@ \
     # NB: the textual targets are compared to oracles.@]@  \
     MODULE: <module>...  @[<v 0># Compile the module and set the @@PTEST_MODULE@@ macro.@]@  \
     LIBS: <module>...    @[<v 0># Don't compile the module but set the @@PTEST_LIBS@@ macro.@]@  \
     PLUGIN: <plugin>...  @[<v 0># Set the @@PTEST_PLUGIN@@ macro.@]@  \
     SCRIPT: <script>...  @[<v 0># Set the @@PTEST_SCRIPT@@ macro.@]@  \
     DEPS: <dependency>...@[<v 0># Set the @@PTEST_DEPS@@ macro and adds a dependency to next sub-test and execnow commands (forward compatibility).@ \
     # NB: a dependency to the included files can be added with this directive.@ \
     # That is not necessary for files mentioned into the command or options when using the %%{dep:<file>} feature of dune.@]@  \
     LOG: <file>...       @[<v 0># Defines targets built by the next sub-test command.@]@  \
     CMD: <command>       @[<v 0># Defines the command to execute for all tests in order to get results to be compared to oracles.@ \
     # NB: the dune feature %%{bin:tool} has to be used to access to a tool of the binary directory of Frama-C.@]@  \
     OPT: <options>       @[<v 0># Defines a sub-test using the 'CMD' definition: <command> <options>@]@  \
     STDOPT: -\"<extra>\"   @[<v 0># Defines a sub-test and remove the extra from the current option.@ \
     # NB: current version does not allow to remove a multiple-extra-argument.@]@  \
     STDOPT: +\"<extra>\"   @[<v 0># Defines a sub-test and appends the extra to the current option.@]@  \
     STDOPT: #\"<extra>\"   @[<v 0># Defines a sub-test and prepends the extra to the current option.@]@  \
     EXIT: <number>       @[<v 0># Defines the exit code required for the next sub-test commands.@]@  \
     FILTER: <cmd>        @[<v 0># Performs a transformation on the test result files before the comparison from the oracles.@ \
     # The oracle will be compared from the standard output of the command: cat <test-output-file> | <cmd> .@ \
     # Chaining multiple filter commands is possible by defining several FILTER directives.@ \
     # An empty command drops the previous FILTER directives.@ \
     # NB: in such a command, the @@PTEST_ORACLE@@ macro is set to the basename of the oracle.@ \
     # This allows running a 'diff' command with the oracle of another test configuration:@ \
     #    FILTER: diff --new-file @@PTEST_SUITE_DIR@@/oracle_configuration/@@PTEST_ORACLE@@ @]@  \
     TIMEOUT: <delay>     @[<v 0># Set a timeout for all sub-test.@]@  \
     NOFRAMAC:            @[<v 0># Drops previous sub-test definitions and considers that there is no defined default sub-test.@]@  \
     GCC:                 @[<v 0># Deprecated.@]@  \
     MACRO: <name> <def>  @[<v 0># Set a definition to the macro @@<name>@@.@]@  \
     @]@ \
     @[<v 1>\
     Default directive values:@ \
     FILEREG: %s@ \
     CMD:     %s@ \
     EXIT:    0@ \
     @]@ \
     @[<v 1>\
     Some predefined macros can be used in test commands:@ \
     @@PTEST_DIR@@          # Path to the test file from the execution directory (depends from -dune-mode option).@ \
     @@PTEST_FILE@@         # Substituted by the test filename.@ \
     @@PTEST_NAME@@         # Basename of the test file.@ \
     @@PTEST_NUMBER@@       # Test command number.@ \
     @@PTEST_CONFIG@@       # Test configuration suffix.@ \
     @@PTEST_SESSION@@      # Set to the value of the environment variable FRAMAC_SESSION.@ \
     @@PTEST_SUITE_DIR@@    # Path to the directory contained the source of the test file (depends from -dune-mode option).@ \
     @@PTEST_RESULT@@       # Shorthand alias to '@@PTEST_SUITE_DIR@@/result@@PTEST_CONFIG@@' (the result directory dedicated to the tested configuration).@ \
     @@PTEST_ORACLE@@       # Basename of the current oracle file (macro only usable in FILTER directives).@ \
     @@PTEST_DEPS@@         # Current list of dependencies defined by the DEPS directive.@ \
     @@PTEST_LIBS@@         # Current list of modules defined by the LIBS directive.@ \
     @@PTEST_MODULE@@       # Current list of modules defined by the MODULE directive.@ \
     @@PTEST_PLUGIN@@       # Current list of plugins defined by the PLUGIN directive.@ \
     @@PTEST_SCRIPT@@       # Current list of ML scripts defined by the SCRIPT directive.@ \
     @@PTEST_SHARE_DIR@@    # Shorthand alias to '@@PTEST_SUITE_DIR@@/../../share (the share directory related to the test suite).@ \
     @]@ \
     Other macros can only be used in test commands (CMD and EXECNOW directives):@  \
     @@PTEST_DEFAULT_OPTIONS@@  # The default option list: %s@  \
     @@PTEST_LOAD_LIBS@@        # The '-load-module' option related to the LIBS directive.@  \
     @@PTEST_LOAD_MODULE@@      # The '-load-module' option related to the MODULE directive.@  \
     @@PTEST_LOAD_PLUGIN@@      # The '-load-module' option related to the PLUGIN directive.@  \
     @@PTEST_LOAD_SCRIPT@@      # The '-load-script' option related to the SCRIPT directive.@  \
     @@PTEST_LOAD_OPTIONS@@     # Shorthand alias to '@@PTEST_LOAD_PLUGIN@@ @@PTEST_LOAD_LIBS@@ @@PTEST_LOAD_MODULE@@ @@PTEST_LOAD_SCRIPT@@' .@  \
     @@PTEST_OPTIONS@@          # The current list of options related to OPT and STDOPT directives (for CMD directives).@  \
     @@frama-c@@                # Shortcut defined as follow: %s@  \
     @@frama-c-cmd@@            # Shortcut defined as follow: %s@  \
     @@frama-c-exe@@            # set to the value of the 'TOPLEVEL_PATH' variable defined in the './tests/ptests_config' file.@  \
     @@FRAMAC_SHARE@@           # set to the value of the 'FRAMAC_SHARE' variable defined in the './tests/ptests_config' file.@  \
     @@DEV_NULL@@               # set to 'NUL' for Windows platforms and to '/dev/null' otherwise.@  \
     @]@ \
     @[<v 1>\
     Examples:@ \
     ptests@ \
     ptests -diff \"echo diff\" -examine        \
     # see again the list of tests that failed@ \
     ptests misc                              \
     # for a single test suite@ \
     ptests tests/misc/alias.c                \
     # for a single test@ \
     ptests -examine tests/misc/alias.c       \
     # to see the differences again@ \
     ptests -v -j 1                           \
     # to check the time taken by each test\
     @]@ @]"
    test_file_regexp
    !default_toplevel
    !macro_default_options
    !macro_frama_c
    !macro_frama_c_cmd

let umsg = "Usage: ptests [options] [names of test suites]";;

let rec argspec =
  [
    "-examine", Arg.Unit (fun () -> behavior := Examine) ,
    " Examine the logs that are different from oracles.";
    "-gui", Arg.Unit (fun () ->
        behavior := Gui;
        n := 1; (* Disable parallelism to see which GUI is launched *)
      ) ,
    " Start the tests in Frama-C's gui.";
    "-update", Arg.Unit (fun () -> behavior := Update) ,
    " Take the current logs as oracles. \
     \n   NB: the default value can be modified in setting the environment variable PTEST_UPDATE to 1";
    "-show", Arg.Unit (fun () -> behavior := Show) ,
    " Show the results of the tests.";
    "-run", Arg.Unit (fun () -> behavior := Run) ,
    " (default) Delete logs, run tests, then examine logs different from \
     oracles.";
    "-v", Arg.Unit (fun () -> incr verbosity),
    " Increase verbosity (up to  twice)" ;
    "-dry-run", Arg.Unit (fun () -> dry_run := true),
    " Do not run commands (use with -v to print all commands which would be run)" ;
    "-diff", Arg.String (fun s -> do_diffs := s;
                          if !use_diff_as_cmp then do_cmp := s),
    "<command>  Use command for diffs" ;
    "-cmp", Arg.String (fun s -> do_cmp:=s),
    "<command>  Use command for comparison";
    "-make", Arg.String (fun s -> do_make := s;),
    "<command> Use command instead of make";
    "-use-diff-as-cmp",
    Arg.Unit (fun () -> use_diff_as_cmp:=true; do_cmp:=!do_diffs),
    " Use the diff command for performing comparisons";
    "-j", Arg.Int
      (fun i -> if i>=0
        then n := i
        else ( lock_printf "Option -j requires nonnegative argument@.";
               exit (-1))),
    "<n>  Use nonnegative integer n for level of parallelism" ;
    "-byte", Arg.Set use_byte,
    " Use bytecode toplevel";
    "-opt", Arg.Clear use_byte,
    " Use native toplevel (default)";
    "-config", Arg.Set_string special_config,
    " <name> Use special configuration and oracles \
     \n   NB: the default value can be modified in setting the environment variable PTEST_CONFIG";
    "-add-options", Arg.Set_string macro_post_options,
    "<options> Add additional options to be passed to the toplevels \
     that will be launched. <options> are added after standard test options";
    "-add-options-pre", Arg.Set_string macro_pre_options,
    "<options> Add additional options to be passed to the toplevels \
     that will be launched. <options> are added before standard test options.";
    "-add-options-post", Arg.Set_string macro_post_options,
    "Synonym of -add-options";
    "-exclude", Arg.String exclude,
    "<name> Exclude a test or a suite from the run";
    "-xunit", Arg.Set xunit,
    " Create a xUnit file named xunit.xml collecting results";
    "-error-code", Arg.Set do_error_code,
    " Exit with error code 1 if tests failed (useful for scripts)";
    "-dune-mode", Arg.Set_int dune_mode,
    " <mode> Run test commands: \
     \n   0 -> from the plugin or frama-c directory \
     \n   1 -> same as mode 0 with some extra ptest directives giving results closer to those obtained with the mode 2 \
     \n   2 -> from the result directories of the current configuration \
     \n   NB: the default value can be modified in setting the environment variable PTEST_DUNE_MODE";
  ]
and help_msg () = Arg.usage (Arg.align argspec) umsg;;

let () =
  Arg.parse
    ((Arg.align
        (List.sort
           (fun (optname1, _, _) (optname2, _, _) ->
              compare optname1 optname2
           ) argspec)
     ) @ ["", Arg.Unit (fun () -> ()), example_msg;])
    make_test_suite umsg

(** split the filename into before including "tests" dir and after including "tests" dir
    NOTA: both part contains "tests" (one as suffix the other as prefix).
*)
let rec get_upper_test_dir initial dir =
  let tests = Filename.dirname dir in
  if tests = dir then
    (* root directory *)
    (fail (Printf.sprintf "Can't find a tests directory below %s" initial))
  else
    let base = Filename.basename dir in
    if base = "tests" then
      dir, "tests"
    else
      let tests, suffix = get_upper_test_dir initial tests in
      tests, Filename.concat suffix base

let rec get_test_path = function
  | [] ->
    if Sys.file_exists "tests" && Sys.is_directory "tests" then "tests", []
    else begin
      Format.eprintf "No test path found. Aborting@.";
      exit 1
    end
  | [f] -> let tests, suffix = get_upper_test_dir f f in
    tests, [suffix]
  | a::l ->
    let tests, l = get_test_path l in
    let a_tests, a = get_upper_test_dir a a in
    if a_tests <> tests
    then fail (Printf.sprintf "All the tests should be inside the same tests directory")
    else tests, a::l

let test_path =
  let files, names = List.partition Sys.file_exists !suites in
  let tests, l = get_test_path files in
  let names = List.map (Filename.concat tests) names in
  suites := names@l;
  Sys.chdir (Filename.dirname tests);
  "tests"

let parse_config_line =
  let regexp_blank = Str.regexp "[ ]+" in
  fun (key, value) ->
    match key with
    | "DEFAULT_SUITES" ->
      let l = str_split regexp_blank value in
      default_suites := List.map (Filename.concat test_path) l
    | "TOPLEVEL_PATH" ->
      toplevel_path := value
    | _ -> default_env key value (* Environnement variable that Frama-C reads*)


(** parse config files *)
let () =
  let config = "tests/ptests_config" in
  if Sys.file_exists config then begin
    try
      (*Parse the plugin configuration file for tests. Format is 'Key=value' *)
      let ch = open_in config in
      let regexp = Str.regexp "\\([^=]+\\)=\\(.*\\)" in
      while true do
        let line = input_line ch in
        match str_string_match2 regexp line 0 with
        | Some (key,value) -> parse_config_line (key, value)
        | None ->
          Format.eprintf "Cannot interpret line '%s' in ptests_config@." line;
          exit 1
      done
    with
    | End_of_file ->
      if !toplevel_path = "" then begin
        Format.eprintf "Missing TOPLEVEL_PATH variable. Aborting.@.";
        exit 1
      end
  end
  else begin
    Format.eprintf
      "Cannot find configuration file %s. Aborting.@." config;
    exit 1
  end

(** Must be done after reading config *)
let () =
  if !use_byte then begin
    match string_del_suffix "frama-c" !toplevel_path with
    | Some path -> toplevel_path := path ^ "frama-c.byte"
    | None ->
      match string_del_suffix "toplevel.opt" !toplevel_path with
      | Some path -> toplevel_path := path ^ "toplevel.byte"
      | None ->
        match string_del_suffix "frama-c-gui" !toplevel_path with
        | Some path -> toplevel_path := path ^ "frama-c-gui.byte"
        | None ->
          match string_del_suffix "viewer.opt" !toplevel_path with
          | Some path -> toplevel_path := path ^ "viewer.byte"
          | None -> ()
  end;
  if !behavior = Gui then begin
    match string_del_suffix "toplevel.opt" !toplevel_path with
    | Some s -> toplevel_path := s ^ "viewer.opt"
    | None ->
      match string_del_suffix "toplevel.byte" !toplevel_path with
      | Some s -> toplevel_path := s ^ "viewer.byte"
      | None ->
        match string_del_suffix "frama-c" !toplevel_path with
        | Some s -> toplevel_path := s ^ "frama-c-gui"
        | None ->
          match string_del_suffix "frama-c.byte" !toplevel_path with
          | Some s -> toplevel_path := s ^ "frama-c-gui.byte"
          | None -> ()
  end

(* redefine name if special configuration expected *)
let redefine_name name =
  if !special_config = "" then name else
    name ^ "_" ^ !special_config

let dir_config_file = redefine_name dir_config_file

let gen_make_file s dir file =
  Filename.concat (Filename.concat dir s) file

module SubDir: sig
  type t

  val get: t -> string

  val create: ?with_subdir:bool -> string (** dirname *) -> t
  (** By default, creates the needed subdirectories if absent.
      Anyway, fails if the given dirname doesn't exists *)

  val make_oracle_file: t -> string -> string
  val make_result_file: t -> string -> string
  val make_file: t -> string -> string

  val result_dirname: string
end = struct
  type t = string

  let get s = s

  let create_if_absent dir =
    if not (Sys.file_exists dir)
    then Unix.mkdir dir 0o750 (** rwxr-w--- *)
    else if not (Sys.is_directory dir)
    then fail (Printf.sprintf "the file %s exists but is not a directory" dir)

  let oracle_dirname = redefine_name "oracle"
  let result_dirname = redefine_name "result"

  let make_result_file = gen_make_file result_dirname
  let make_oracle_file = gen_make_file oracle_dirname
  let make_file = Filename.concat

  let create ?(with_subdir=true) dir =
    if not (Sys.file_exists dir && Sys.is_directory dir)
    then fail (Printf.sprintf "the directory %s must be an existing directory" dir);
    if (with_subdir) then begin
      create_if_absent (Filename.concat dir result_dirname);
      create_if_absent (Filename.concat dir oracle_dirname)
    end;
    dir

end

let mk_symbolic_link =
  let symlink = match !dune_mode with
    | 0 | 1 -> fun ~unlink ~to_dir ~link_dst:_ ~link ->
      if unlink then begin
        if !verbosity >= 4 then lock_printf "removing symbolic link %s/%s@." (Unix.getcwd ()) link;
        Unix.unlink link;
      end
    | _ -> fun ~unlink ~to_dir ~link_dst ~link ->
      if !verbosity >= 4 then lock_printf "creating symbolic link %s/%s -> %s@." (Unix.getcwd ()) link link_dst;
      if unlink then
        Unix.unlink link;
      Unix.symlink ~to_dir link_dst link
  in
  let symlink_there = match !dune_mode with
    | 0 | 1 -> fun ~link ->
      if !verbosity >= 4 then lock_printf "removing symbolic link %s/%s@." (Unix.getcwd ()) link;
      Unix.unlink link
    | _ -> fun ~link:_ -> ()
  in
  let regexp_ignored_dir = Str.regexp "^\\(result\\|oracle\\)" in
  if not (Unix.has_symlink ()) then
    fail "unable to create symbolic links!";
  fun directory file ->
    let dst = SubDir.make_file directory file in
    let infos = Unix.stat dst in
    let link = SubDir.make_result_file directory file in
    let link_dst = "../" ^ file in
    let mk_symlink ~to_dir =
      if is_nonexisting_link link then (* not there *)
        symlink ~unlink:false ~to_dir ~link_dst ~link
      else if String.(link_dst <> (Unix.readlink link)) then (* goes elsewhere *)
        symlink ~unlink:true ~to_dir ~link_dst ~link
      else symlink_there ~link (* is already there *)
    in
    match infos.st_kind with
    | Unix.S_LNK
    | Unix.S_REG ->
      mk_symlink ~to_dir:false
    | Unix.S_DIR ->
      if str_string_match regexp_ignored_dir file 0 then ()
      else mk_symlink ~to_dir:true
    | _ -> ()

type does_expand = {
  has_ptest_file : bool;
  has_ptest_opt : bool;
  has_frama_c_exe : bool;
}

module Macros =
struct
  module StringMap = Map.Make (String)
  open StringMap

  type t = string StringMap.t

  let add_defaults ~defaults macros =
    StringMap.merge (fun _k default cur ->
        match cur with
        | Some _ -> cur
        | _ -> default) defaults macros

  let empty = StringMap.empty

  let print_macros macros =
    lock_printf "%% Macros (%d):@."  (StringMap.cardinal macros);
    StringMap.iter (fun key data -> lock_printf "%% - %s -> %s@." key data) macros;
    lock_printf "%% End macros@."

  let does_expand =
    let macro_regex = Str.regexp "@\\([-A-Za-z_0-9]+\\)@" in
    fun macros s ->
      let has_ptest_file = ref false in
      let has_ptest_opt = ref false in
      let has_ptest_options = ref false in
      let has_frama_c_exe = ref false in
      if !verbosity >= 4 then lock_printf "%% Expand: %s@." s;
      if !verbosity >= 5 then print_macros macros;
      let nb_loops = ref 0 in
      let rec aux s =
        if !nb_loops > 100 then
          fail "Possible infinite recursion in macro expands"
        else incr nb_loops ;
        let expand_macro = function
          | Str.Text s -> s
          | Str.Delim s ->
            match str_string_match1 macro_regex s 0  with
            | Some macro -> begin
                (match macro with
                 | "PTEST_FILE" -> has_ptest_file := true
                 | "PTEST_OPT" -> has_ptest_opt := true
                 | "PTEST_OPTIONS" -> has_ptest_options := true
                 | "frama-c-exe" -> has_frama_c_exe := true
                 | _ -> ());
                if !verbosity >= 5 then lock_printf "%%     - macro is %s\n%!" macro;
                try
                  let replacement = find macro macros in
                  if !verbosity >= 4 then
                    lock_printf "%%     - replacement for %s is %s\n%!" macro replacement;
                  aux replacement
                with Not_found -> s
              end
            | None -> s
        in
        String.concat "" (List.map expand_macro (Str.full_split macro_regex s))
      in
      let r =
        try aux s
        with e ->
          lock_eprintf "Uncaught exception %s\n%!" (Printexc.to_string e);
          raise e
      in
      if !verbosity >= 4 then lock_printf "%% Expansion result: %s@." r;
      { has_ptest_file= !has_ptest_file;
        has_ptest_opt= !has_ptest_opt;
        has_frama_c_exe= !has_frama_c_exe;
      }, r

  let expand macros s =
    snd (does_expand macros s)

  let expand_directive =
    let deprecated_opts = "(-load-module|-load-script)" in
    let contains_deprecated_opts = str_string_contains_option "\\(-load-module\\|-load-script\\)" in
    fun ~file macros s ->
      let contains = contains_deprecated_opts s 0 in
      if contains then lock_eprintf "%s: DEPRECATED direct use of %s option: %s@.Please use PLUGIN, MODULE, SCRIPT or LIBS directive instead of the deprecated option.@." file deprecated_opts s;
      expand macros s


  let get ?(default="") name macros =
    try find name macros with Not_found -> default

  let add_list l map =
    List.fold_left (fun acc (k,v) ->
        if !verbosity >= 4 then
          lock_printf "%%   - Adds macro %s with definition %s@." k v;
        add k v acc) map l

  let add_expand name def macros =
    add name (expand macros def) macros

  let append_expand name def macros =
    add name (get name macros ^ expand macros def) macros
end

type execnow =
  {
    ex_cmd: string;      (** command to launch *)
    ex_make_cmd: bool;   (** is it a make command *)
    ex_macros: Macros.t; (** current macros *)
    ex_log: string list; (** log files *)
    ex_bin: string list; (** bin files *)
    ex_dir: SubDir.t;    (** directory of test suite *)
    ex_file: string;     (** test file*)
    ex_once: bool;       (** true iff the command has to be executed only once
                             per config file (otherwise it is executed for
                             every file of the test suite) *)
    ex_done: bool ref;   (** has the command been already fully executed.
                             Shared between all copies of this EXECNOW. Do
                             NOT use a mutable field here, as execnows
                             are duplicated using OCaml 'with' syntax. *)
    ex_timeout: string;
  }


(** configuration of a directory/test. *)
type cmd = {
  toplevel: string;
  make_cmd: bool;   (** is it a make command *)
  opts: string;
  macros: Macros.t;
  exit_code: string option;
  logs:string list;
  timeout:string
}

module StringSet = Set.Make (String)

type config =
  { dc_test_regexp: string; (** regexp of test files. *)
    dc_execnow    : execnow list; (** command to be launched before
                                       the toplevel(s)
                                  *)
    dc_load_script: string; (** load libs options. *)
    dc_load_libs: string; (** load libs options. *)
    dc_load_module: string; (** load module options. *)
    dc_cmxs_module: StringSet.t; (** compiled modules. *)
    dc_macros: Macros.t; (** existing macros. *)
    dc_default_toplevel   : string;
    (** full path of the default toplevel. *)
    dc_filter     : string option; (** optional filter to apply to
                                       standard output *)
    dc_exit_code  : string option; (** required exit code *)
    dc_commands   : cmd list;
    (** toplevel full path, options to launch the toplevel on, and list
        of output files to monitor beyond stdout and stderr. *)
    dc_dont_run   : bool;
    dc_framac     : bool;
    dc_default_log: string list;
    dc_timeout: string
  }

let launch command_string =
  if !dry_run then 0 (* do not run command; return as if no error *)
  else
    let result = system command_string in
    match result with
    | Unix.WEXITED 127 ->
      lock_printf "%% Couldn't execute command. Retrying once.@.";
      Thread.delay 0.125;
      ( match system command_string with
          Unix.WEXITED r when r <> 127 -> r
        | _ -> lock_printf "%% Retry failed with command:@\n%s@\nStopping@."
                 command_string ;
          exit 1 )
    | Unix.WEXITED r -> r
    | Unix.WSIGNALED s ->
      lock_printf
        "%% SIGNAL %d received while executing command:@\n%s@\nStopping@."
        s command_string ;
      exit 1
    | Unix.WSTOPPED s ->
      lock_printf
        "%% STOP %d received while executing command:@\n%s@\nStopping@."
        s command_string;
      exit 1

let dev_null = if Sys.os_type = "Win32" then "NUL" else "/dev/null"

let default_filter = match !dune_mode with
  | 1 -> Some "sed -e \"s| share/| FRAMAC_SHARE/|g; s|@PTEST_DIR@/||g; s|result@PTEST_CONFIG@/||g\""
  | _ -> None

let log_default_filter = match default_filter with
  | Some filter ->
    let redirection = Str.regexp " > " in
    fun s -> str_global_replace redirection (" | " ^ filter ^ " > ") s
  | None -> fun s -> s

module Test_config: sig
  val scan_directives: drop:bool ->
    SubDir.t -> file:string -> Scanf.Scanning.in_channel -> config -> config
  val current_config: unit -> config
  val scan_test_file: config -> SubDir.t -> string -> config
end = struct

  let default_options =
    match !dune_mode with
    | 0 -> !macro_default_options
    | _ -> !macro_default_options ^ " -add-symbolic-path @PTEST_SESSION@:."

  let default_macros () =
    let l = [
      "frama-c-exe",  !toplevel_path;
      "frama-c-cmd",  !macro_frama_c_cmd;
      "frama-c",      !macro_frama_c;
      "DEV_NULL",     dev_null;
      "FRAMAC_SHARE",           get_default_env "FRAMAC_SHARE" "";
      "PTEST_SESSION",          get_default_env "FRAMAC_SESSION" "";
      "PTEST_DEFAULT_OPTIONS",  default_options;
      "PTEST_OPTIONS",          !macro_options;
      "PTEST_PRE_OPTIONS",      !macro_pre_options;
      "PTEST_POST_OPTIONS",     !macro_post_options;
      "PTEST_MAKE_MODULE", "make -s";
      "PTEST_DEPS", "";
      "PTEST_LIBS", "";
      "PTEST_MODULE", "";
      "PTEST_PLUGIN", "";
      "PTEST_SCRIPT", "";
    ]
    in
    Macros.add_list l Macros.empty

  let default_config () =
    { dc_test_regexp = test_file_regexp ;
      dc_macros = default_macros ();
      dc_execnow = [];
      dc_filter = default_filter ;
      dc_exit_code = None;
      dc_default_toplevel = !default_toplevel;
      dc_commands = [ { toplevel= !default_toplevel; make_cmd=false; opts=""; macros=Macros.empty; exit_code=None; logs= []; timeout= ""} ];
      dc_dont_run = false;
      dc_load_module = "";
      dc_load_libs = "";
      dc_load_script = "";
      dc_cmxs_module = StringSet.empty;
      dc_framac = true;
      dc_default_log = [];
      dc_timeout = "";
    }

  let scan_execnow ~warn ~once ~file dir ex_macros ex_timeout (s:string) =
    if once=false then
      lock_eprintf "%s: using EXEC directive (DEPRECATED): %s@."
        file s;
    let rec aux (s:execnow) =
      try
        Scanf.sscanf s.ex_cmd "%_[ ]LOG%_[ ]%[-A-Za-z0-9_',+=:.\\@@]%_[ ]%s@\n"
          (fun name cmd ->
             aux { s with ex_cmd = cmd; ex_log = name :: s.ex_log })
      with Scanf.Scan_failure _ ->
      try
        Scanf.sscanf s.ex_cmd "%_[ ]BIN%_[ ]%[-A-Za-z0-9_.\\@@]%_[ ]%s@\n"
          (fun name cmd ->
             aux { s with ex_cmd = cmd; ex_bin = name :: s.ex_bin })
      with Scanf.Scan_failure _ ->
      try
        Scanf.sscanf s.ex_cmd "%_[ ]make%_[ ]%s@\n"
          (fun cmd ->
             (* It should be better to use a specific macro into the command (such as @MAKE@) for that. *)
             let s = aux ({ s with ex_cmd = cmd; }) in
             let r = { s with
                       ex_cmd = !do_make^" "^cmd;
                       ex_make_cmd = true
                     }
             in
             if warn then
               Format.eprintf "%s: EXEC%s directive with a make command (DEPRECATED): %s@."
                 file (if once then "NOW" else "") r.ex_cmd;
             r)
      with Scanf.Scan_failure _ ->
        s
    in
    let execnow = aux
        { ex_cmd = s;
          ex_make_cmd = false;
          ex_macros;
          ex_log = [];
          ex_bin = [];
          ex_dir = dir;
          ex_file = file;
          ex_once = once;
          ex_done = ref false;
          ex_timeout;
        }
    in
    if warn && execnow.ex_log = [] && execnow.ex_bin = [] then
      Format.eprintf "%s: EXEC%s without LOG nor BIN target (DEPRECATED): %s@."
        file (if once then "NOW" else "") s;
    execnow

  type parsing_env = {
    current_default_toplevel: string;
    current_default_log: string list;
    current_default_cmds: cmd list;
  }

  let default_parsing_env = ref {
      current_default_toplevel = "" ;
      current_default_log = [] ;
      current_default_cmds = []
    }

  let set_default_parsing_env config =
    default_parsing_env := {
      current_default_toplevel = config.dc_default_toplevel;
      current_default_log = config.dc_default_log;
      current_default_cmds = List.rev config.dc_commands;
    }

  let make_custom_opts =
    let space = Str.regexp " " in
    fun ~file stdopts s ->
      let rec aux opts s =
        try
          Scanf.sscanf s "%_[ ]%1[+#\\-]%_[ ]%S%_[ ]%s@\n"
            (fun c opt rem ->
               match c with
               | "+" -> aux (opts @ [ opt ]) rem (* appends [opt] *)
               | "#" -> aux (opt :: opts) rem (* preppends [opt] *)
               | "-" -> aux (List.filter (fun x -> x <> opt) opts) rem
               | _ -> assert false (* format of scanned string disallow it *))
        with
        | Scanf.Scan_failure _ ->
          if s <> "" then
            lock_eprintf "%s: unknown STDOPT configuration string: %s@."
              file s;
          opts
        | End_of_file -> opts
      in
      (* NB: current settings does not allow to remove a multiple-argument
         option (e.g. -verbose 2).
      *)
      let opts = aux (str_split space stdopts) s in
      String.concat " " opts

  (* how to process options *)
  let config_exec ~warn ~once ~file dir s current =
    let s = Macros.expand_directive ~file current.dc_macros s in
    { current with
      dc_execnow =
        scan_execnow ~warn ~once ~file dir current.dc_macros current.dc_timeout s :: current.dc_execnow }

  let config_macro =
    let regex = Str.regexp "[ \t]*\\([^ \t@]+\\)\\([ \t]+\\(.*\\)\\|$\\)" in
    fun ~file _dir s current ->
      let s = Macros.expand_directive ~file current.dc_macros s in
      Mutex.lock str_mutex;
      if Str.string_match regex s 0 then begin
        let name = Str.matched_group 1 s in
        let def =
          try Str.matched_group 3 s with Not_found -> (* empty text *) ""
        in
        Mutex.unlock str_mutex;
        if !verbosity >= 4 then
          lock_printf "%%   - New macro %s with definition %s\n%!" name def;
        { current with dc_macros = Macros.add_expand name def current.dc_macros }
      end else begin
        Mutex.unlock str_mutex;
        lock_eprintf "%s: cannot understand MACRO definition: %s\n%!" file s;
        current
      end

  let update_make_module_name s =
    let s = (Filename.remove_extension s) ^ (if !use_byte then ".cmo" else ".cmxs") in
    if "." = Filename.dirname s then "@PTEST_MAKE_DIR@/" ^  s else s

  let update_module_libs_name s =
    let s = (Filename.remove_extension s) ^ (if !use_byte then ".cmo" else ".cmxs") in
    if "." = Filename.dirname s then "@PTEST_SUITE_DIR@/" ^  s else s

  let add_make_modules ~file dir deps current =
    let deps,current = List.fold_left (fun ((deps,curr) as acc) s ->
        let s = update_make_module_name s in
        if StringSet.mem s curr.dc_cmxs_module then acc
        else
          (deps ^ " " ^ s),
          { curr with dc_cmxs_module = StringSet.add s curr.dc_cmxs_module })
        ("",current) deps
    in
    if String.(deps = "") then current
    else begin
      let make_cmd = Macros.expand current.dc_macros "@PTEST_MAKE_MODULE@" in
      config_exec ~warn:false ~once:true ~file dir (make_cmd ^ deps) current
    end

  let update_macros update_name load_option macro_def macro_load_def current modules =
    let def = String.concat "," modules in
    let load_def = if String.(def = "") then "" else
        load_option ^ (String.concat "," (List.map update_name modules))
    in
    if !verbosity >= 3 then Format.printf "%% %s: %s@." macro_def def ;
    let dc_macros = Macros.add_list [ macro_def, def ;
                                      macro_load_def, load_def ;
                                    ] current.dc_macros in
    { current with dc_macros }

  let update_script_name s =
    let s = (Filename.remove_extension s) ^ ".ml" in
    if "." = Filename.dirname s then "@PTEST_DIR@/" ^  s else s

  let update_module_macros =
    update_macros update_module_libs_name "-load-module=" "PTEST_MODULE" "PTEST_LOAD_MODULE"

  let update_libs_macros =
    update_macros update_module_libs_name "-load-module=" "PTEST_LIBS" "PTEST_LOAD_LIBS"

  let update_script_macros =
    update_macros update_script_name "-load-script=" "PTEST_SCRIPT" "PTEST_LOAD_SCRIPT"

  let update_plugin_macros =
    update_macros (fun name -> name) "-load-module=" "PTEST_PLUGIN" "PTEST_LOAD_PLUGIN"

  let config_deps ~file dir s current =
    let macro_def = "PTEST_DEPS" in
    let def = Macros.expand_directive ~file current.dc_macros s in
    if !verbosity >= 3 then Format.printf "%% %s: %s@." macro_def def ;
    let dc_macros = Macros.add_list [ macro_def, def ;
                                    ] current.dc_macros in
    { current with dc_macros }

  let config_module ~file dir s current =
    let s = Macros.expand_directive ~file current.dc_macros s in
    let deps = str_split_list s in
    let current = update_module_macros current deps in
    add_make_modules ~file dir deps current

  let config_libs_script_plugin update ~file dir s current =
    let s = Macros.expand_directive ~file current.dc_macros s in
    let deps = str_split_list s in
    update current deps

  let config_options =
    [ "CMD",
      (fun ~file _ s current ->
         let s = Macros.expand_directive ~file current.dc_macros s in
         { current with dc_default_toplevel = s});

      "OPT",
      (fun ~file _ s current ->
         if not (current.dc_framac) then
           lock_eprintf
             "%s: a NOFRAMAC directive has been defined before a sub-test defined by a 'OPT' directive (That NOFRAMAC directive could be misleading.).@."
             file;
         let s = Macros.expand_directive ~file current.dc_macros s in
         let t =
           { toplevel= current.dc_default_toplevel;
             make_cmd = false;
             opts= s;
             logs= current.dc_default_log;
             exit_code= current.dc_exit_code;
             macros= current.dc_macros;
             timeout= current.dc_timeout}
         in
         { current with
           dc_default_log = !default_parsing_env.current_default_log;
           dc_commands = t :: current.dc_commands });

      "STDOPT",
      (fun ~file _ s current ->
         if not current.dc_framac then
           lock_eprintf
             "%s: a NOFRAMAC directive has been defined before a sub-test defined by a 'STDOPT' directive (That NOFRAMAC directive could be misleading.).@."
             file;
         let s = Macros.expand_directive ~file current.dc_macros s in
         let new_top =
           List.map
             (fun command ->
                { toplevel = current.dc_default_toplevel;
                  make_cmd = false;
                  opts= make_custom_opts ~file command.opts s;
                  logs= command.logs @ current.dc_default_log;
                  macros= current.dc_macros;
                  exit_code = current.dc_exit_code;
                  timeout= current.dc_timeout
                })
             !default_parsing_env.current_default_cmds
         in
         { current with dc_commands = new_top @ current.dc_commands;
                        dc_default_log = !default_parsing_env.current_default_log });

      "FILEREG",
      (fun ~file _ s current ->
         let s = Macros.expand_directive ~file current.dc_macros s in
         { current with dc_test_regexp = s });

      "FILTER",
      (fun ~file _ s current ->
         let s = Macros.expand_directive ~file current.dc_macros s in
         let s = trim_right s in
         match current.dc_filter with
         | None when s="" -> { current with dc_filter = None }
         | None           -> { current with dc_filter = Some s }
         | Some filter    -> { current with dc_filter = Some (s ^ " | " ^ filter) });

      "EXIT",
      (fun ~file _ s current ->
         let s = Macros.expand_directive ~file current.dc_macros s in
         { current with dc_exit_code = Some s });

      "GCC",
      (fun ~file _ _ acc ->
         lock_eprintf "%s: GCC directive (DEPRECATED)@." file;
         acc);

      "COMMENT",
      (fun ~file:_ _ _ acc -> acc);

      "DONTRUN",
      (fun ~file:_ _ s current -> { current with dc_dont_run = true });

      "EXECNOW", config_exec ~warn:true ~once:true;
      "EXEC", config_exec ~warn:true ~once:false;

      "MACRO", config_macro;

      "MODULE", config_module;

      "DEPS",   config_deps;

      "LIBS",   config_libs_script_plugin update_libs_macros;
      "SCRIPT", config_libs_script_plugin update_script_macros;
      "PLUGIN", config_libs_script_plugin update_plugin_macros;

      "LOG",
      (fun ~file _ s current ->
         let s = Macros.expand_directive ~file current.dc_macros s in
         { current with dc_default_log = s :: current.dc_default_log });

      "TIMEOUT",
      (fun ~file _ s current ->
         let s = Macros.expand_directive ~file current.dc_macros s in
         { current with dc_timeout = s });

      "NOFRAMAC",
      (fun ~file _ _ current ->
         if current.dc_commands <> [] && current.dc_framac then
           lock_eprintf
             "%s: a NOFRAMAC directive has the effect of ignoring previous defined sub-tests (by some 'OPT' or 'STDOPT' directives that seems misleading). @."
             file;
         { current with dc_commands = []; dc_framac = false; });
    ]

  (** the pattern that ends the parsing of options in a test file *)
  let end_comment = Str.regexp ".*\\*/"

  let scan_directives ~drop dir ~file scan_buffer default =
    set_default_parsing_env default;
    let r = ref { default with dc_commands = [] } in
    let treat_line s =
      try
        Scanf.sscanf s "%[ *]%[A-Za-z0-9]: %s@\n"
          (fun _ name opt ->
             try
               let directive = List.assoc name config_options in
               if not drop then
                 r := directive ~file dir opt !r;
             with Not_found ->
               lock_eprintf "@[%s: unknown configuration option: %s@\n%!@]" file name)
      with
      | Scanf.Scan_failure _ ->
        if str_string_match end_comment s 0
        then raise End_of_file
        else ()
      | End_of_file -> (* ignore blank lines. *) ()
    in
    try
      while true do
        if Scanf.Scanning.end_of_input scan_buffer then raise End_of_file;
        Scanf.bscanf scan_buffer "%s@\n" treat_line
      done;
      assert false
    with
      End_of_file ->
      (match !r.dc_commands with
       | [] when !r.dc_framac -> { !r with dc_commands = default.dc_commands }
       | l -> { !r with dc_commands = List.rev l })

  let split_config = Str.regexp ",[ ]*"

  let is_config name =
    let prefix = "run.config" in
    let len = String.length prefix in
    String.length name >= len && String.sub name 0 len = prefix

  let scan_test_file default dir f =
    let f = SubDir.make_file dir f in
    let exists_as_file =
      try
        (Unix.lstat f).Unix.st_kind = Unix.S_REG
      with Unix.Unix_error _ | Sys_error _ -> false
    in
    if exists_as_file then begin
      let scan_buffer = Scanf.Scanning.open_in f in
      let rec scan_config () =
        (* space in format string matches any number of whitespace *)
        Scanf.bscanf scan_buffer " /* %s@\n"
          (fun names ->
             let is_current_config name =
               name = "run.config*" ||
               name = "run.config" && !special_config = ""  ||
               name = "run.config_" ^ !special_config
             in
             let configs = str_split split_config (String.trim names) in
             if List.exists is_current_config configs then
               (* Found options for current config! *)
               scan_directives ~drop:false dir ~file:f scan_buffer default
             else (* config name does not match: eat config and continue.
                     But only if the comment is still opened by the end of
                     the line and we are indeed reading a config
                  *)
               (if List.exists is_config configs &&
                   not (str_string_match end_comment names 0) then
                  ignore (scan_directives ~drop:true dir ~file:f scan_buffer default);
                scan_config ()))
      in
      try
        let options =  scan_config () in
        Scanf.Scanning.close_in scan_buffer;
        options
      with End_of_file | Scanf.Scan_failure _ ->
        Scanf.Scanning.close_in scan_buffer;
        default
    end else
      (* if the file has disappeared, don't try to run it... *)
      { default with dc_dont_run = true }

  (* test for a possible toplevel configuration. *)
  let current_config () =
    let general_config_file = Filename.concat test_path dir_config_file in
    if Sys.file_exists general_config_file
    then begin
      let scan_buffer = Scanf.Scanning.from_file general_config_file in
      scan_directives ~drop:false
        (SubDir.create ~with_subdir:false Filename.current_dir_name)
        ~file:general_config_file
        scan_buffer
        (default_config ())
    end
    else default_config ()

end

type toplevel_command =
  { macros: Macros.t;
    log_files: string list;
    file : string ;
    nb_files : int ;
    options : string ;
    toplevel: string ;
    make_cmd: bool ;
    filter : string option ;
    exit_code : int ;
    directory : SubDir.t ;
    n : int;
    execnow:bool;
    timeout: string;
  }

type command =
  | Toplevel of toplevel_command
  | Target of execnow * command Queue.t

type log = Err | Res

type diff =
  | Command_error of toplevel_command * log
  | Target_error of execnow
  | Log_error of SubDir.t (** directory *) * string (** test file *) * string (** log file *)

type cmps =
  | Cmp_Toplevel of toplevel_command * bool (** returns with the required exit_code *)
  | Cmp_Log of SubDir.t (** directory *) * string (** test file *) * string (** log file *)

type shared =
  { lock : Mutex.t ;
    mutable building_target : bool ;
    target_queue : command Queue.t ;
    commands_empty : Condition.t ;
    work_available : Condition.t ;
    diff_available : Condition.t ;
    mutable commands : command Queue.t ; (* file, options, number *)
    cmps : cmps Queue.t ;
    (* command that has finished its execution *)
    diffs : diff Queue.t ;
    (* cmp that showed some difference *)
    mutable commands_finished : bool ;
    mutable cmp_finished : bool ;
    mutable summary_time : float ;
    mutable summary_ret : int ; (* number of run with the required exit code *)
    mutable summary_run : int ;
    mutable summary_ok : int ;
    mutable summary_log : int;
  }

let shared =
  { lock = Mutex.create () ;
    building_target = false ;
    target_queue = Queue.create () ;
    commands_empty = Condition.create () ;
    work_available = Condition.create () ;
    diff_available = Condition.create () ;
    commands = Queue.create () ;
    cmps = Queue.create () ;
    diffs = Queue.create () ;
    commands_finished = false ;
    cmp_finished = false ;
    summary_time = (Unix.times()).Unix.tms_cutime ;
    summary_run = 0 ;
    summary_ret = 0 ;
    summary_ok = 0 ;
    summary_log = 0 }

let unlock () = Mutex.unlock shared.lock

let lock () = Mutex.lock shared.lock

let update_log_files dir file =
  mv (SubDir.make_result_file dir file) (SubDir.make_oracle_file dir file)

let dune_feature_cmd = (* removes dune feature such as %{deps:...} *)
  let dune_cmd_features = Str.regexp "%{[a-z][a-z-]*:\\([^}]*\\)}" in
  let dune_bin_features = Str.regexp "%{bin:\\([^}]*\\)}" in
  let dune_bin_subst = (Filename.dirname !toplevel_path) ^ "/\\1" in
  fun cmd ->
    let cmd = str_global_replace dune_bin_features dune_bin_subst cmd in
    str_global_replace dune_cmd_features "\\1" cmd

module Cmd : sig

  val log_prefix : toplevel_command -> string
  val oracle_prefix : toplevel_command -> string

  val expand_macros : execnow:bool -> defaults:Macros.t -> toplevel_command -> toplevel_command

  (* [basic_command_string cmd] does not redirect the outputs, and does
     not overwrite the result files *)
  val basic_command_string : toplevel_command -> string

  val command_string : toplevel_command -> string

  val update_toplevel_command : toplevel_command -> unit

  val get_ptest_dir : toplevel_command -> string

  val remove_results : toplevel_command -> unit

end = struct

  let catenate_number nb_files prefix n =
    if nb_files > 1
    then prefix ^ "." ^ (string_of_int n)
    else prefix

  let name_without_extension command =
    try
      (Filename.chop_extension command.file)
    with
      Invalid_argument _ ->
      fail ("this test file does not have any extension: " ^
            command.file)

  let gen_prefix gen_file cmd =
    let prefix = gen_file cmd.directory (name_without_extension cmd) in
    catenate_number cmd.nb_files prefix cmd.n

  let log_prefix = gen_prefix SubDir.make_result_file
  let oracle_prefix = gen_prefix SubDir.make_oracle_file

  let get_ptest_file = match !dune_mode with
    | 0 | 1 -> fun cmd -> SubDir.make_file cmd.directory cmd.file
    | _ -> fun cmd -> Filename.basename cmd.file

  let get_ptest_dir = match !dune_mode with
    | 0 | 1 -> fun cmd -> SubDir.get cmd.directory
    | _ -> fun _ -> "."

  let get_ptest_suite_dir = match !dune_mode with
    | 0 | 1 -> fun cmd -> SubDir.get cmd.directory
    | _ -> fun _ -> ".."

  let ptest_share_dir = match !dune_mode with
    | 0 | 1 -> "./share"
    | _ -> "../../../share"

  let get_ptest_result = match !dune_mode with
    | 0 | 1 ->  fun cmd -> SubDir.get cmd.directory ^ "/" ^ SubDir.result_dirname
    | _ -> fun _ -> "."

  let get_ptest_toplevel = match !dune_mode with
    | 0 | 1 -> fun _ s -> s
    | _ -> fun cmd s ->
      if cmd.make_cmd then s
      else Format.sprintf "(cd %s && (%s))" (SubDir.make_result_file cmd.directory "") s

  let expand_macros =
    fun ~execnow ~defaults cmd ->
    let ptest_config =
      if !special_config = "" then "" else "_" ^ !special_config
    in
    let ptest_file = get_ptest_file cmd in
    let ptest_name =
      try Filename.chop_extension cmd.file
      with Invalid_argument _ -> cmd.file
    in
    let ptest_file = Filename.sanitize ptest_file in
    let ptest_load_plugin = Macros.get "PTEST_LOAD_PLUGIN" cmd.macros in
    let ptest_load_module = Macros.get "PTEST_LOAD_MODULE" cmd.macros in
    let ptest_load_libs = Macros.get "PTEST_LOAD_LIBS" cmd.macros in
    let ptest_load_script = Macros.get "PTEST_LOAD_SCRIPT" cmd.macros in
    let macros =
      [ "PTEST_CONFIG", ptest_config;
        "PTEST_DIR", get_ptest_dir cmd;
        "PTEST_SHARE_DIR", ptest_share_dir;
        "PTEST_SUITE_DIR", get_ptest_suite_dir cmd;
        "PTEST_MAKE_DIR", SubDir.get cmd.directory;
        "PTEST_RESULT", get_ptest_result cmd;
        "PTEST_FILE", ptest_file;
        "PTEST_NAME", ptest_name;
        "PTEST_NUMBER", string_of_int cmd.n;
        "PTEST_OPT", cmd.options;
        "PTEST_LOAD_OPTIONS", (String.concat " "
                                 [ ptest_load_plugin ;
                                   ptest_load_libs ;
                                   ptest_load_module ;
                                   ptest_load_script ; ])
      ]
    in
    let macros = Macros.add_list macros cmd.macros in
    let macros = Macros.add_defaults ~defaults macros in
    let process_macros s = Macros.expand macros s in
    let toplevel =
      let toplevel = log_default_filter cmd.toplevel in
      let in_toplevel,toplevel = Macros.does_expand macros toplevel in
      if cmd.execnow || in_toplevel.has_ptest_opt then toplevel
      else begin
        let has_ptest_file,options =
          let in_option,options = Macros.does_expand macros cmd.options in
          (in_option.has_ptest_file || in_toplevel.has_ptest_file),
          (if in_toplevel.has_frama_c_exe then
             [ process_macros "@PTEST_PRE_OPTIONS@" ;
               options ;
               process_macros "@PTEST_POST_OPTIONS@" ;
             ]
           else [ options ])
        in
        String.concat " " (toplevel::(if has_ptest_file then options else ptest_file::options))
      end
    in
    let toplevel = get_ptest_toplevel cmd (dune_feature_cmd toplevel) in
    { cmd with
      macros;
      toplevel;
      options = ""; (* no more usable *)
      log_files = List.map process_macros cmd.log_files;
      filter =
        match cmd.filter with
        | None -> None
        | Some filter -> Some (process_macros filter)
    }

  let basic_command_string =
    fun command ->
    let raw_command =
      (* necessary until OPT are using direct -load-module option *)
      if !use_byte then opt_to_byte_options command.toplevel
      else command.toplevel
    in
    if command.timeout = "" then raw_command
    else "ulimit -t " ^ command.timeout ^ " && " ^ raw_command

  let command_string command =
    let log_prefix = log_prefix command in
    let reslog,errlog = match command.filter with
      | None -> log_prefix ^ ".res.log", log_prefix ^ ".err.log"
      | Some _ ->log_prefix ^ ".res.unfiltered-log", log_prefix ^ ".err.unfiltered-log"
    in
    let reslog = Filename.sanitize reslog in
    let errlog = Filename.sanitize errlog in
    let command_str = basic_command_string command in
    let command_str =
      command_str ^ " >" ^ reslog ^ " 2>" ^ errlog
    in
    let command_str =
      match command.timeout with
      | "" -> command_str
      | s ->
        Printf.sprintf
          "%s; if test $? -gt 127; then \
           echo 'TIMEOUT (%s); ABORTING EXECUTION' > %s; \
           fi"
          command_str s errlog
    in
    command_str

  let update_toplevel_command command =
    let log_prefix = log_prefix command in
    let oracle_prefix = oracle_prefix command in
    let update_oracle log oracle =
      try
        if is_file_empty_or_nonexisting log then
          (* No, remove the oracle *)
          unlink ~silent:false oracle
        else
          (* Yes, update the oracle*)
          mv log oracle
      with (* Possible error in [is_file_empty] *)
        Unix.Unix_error _ -> ()
    in
    (* Update res.oracle and err.oracle *)
    update_oracle (log_prefix ^ ".res.log") (oracle_prefix ^ ".res.oracle");
    update_oracle (log_prefix ^ ".err.log") (oracle_prefix ^ ".err.oracle");
    (* Update files related to LOG directives *)
    List.iter (update_log_files command.directory) command.log_files

  let remove_results cmd =
    let log_prefix = log_prefix cmd in
    unlink (log_prefix ^ ".res.log ");
    unlink (log_prefix ^ ".err.log ");
    let unlink_log_files dir file =
      unlink (SubDir.make_result_file dir file)
    in
    List.iter (unlink_log_files cmd.directory) cmd.log_files

end

let rec update_command = function
  | Toplevel cmd -> Cmd.update_toplevel_command cmd
  | Target (execnow,cmds) ->
    List.iter (update_log_files execnow.ex_dir) execnow.ex_log;
    Queue.iter update_command cmds

let remove_execnow_results execnow =
  List.iter
    (fun f -> unlink (SubDir.make_result_file execnow.ex_dir f))
    (execnow.ex_bin @ execnow.ex_log)

module Make_Report(M:sig type t end)=struct
  module H=Hashtbl.Make
      (struct
        type t = toplevel_command
        let project cmd = (cmd.directory,cmd.file,cmd.n)
        let compare c1 c2 = compare (project c1) (project c2)
        let equal c1 c2 =  (project c1)=(project c2)
        let hash c = Hashtbl.hash (project c)
      end)
  let tbl = H.create 774
  let m = Mutex.create ()
  let record cmd (v:M.t) =
    if !xunit then begin
      Mutex.lock m;
      H.add tbl cmd v;
      Mutex.unlock m
    end
  let iter f =
    Mutex.lock m;
    H.iter f tbl;
    Mutex.unlock m
  let find k = H.find tbl k
  let remove k = H.remove tbl k

end

module Report_run=Make_Report(struct type t=int*float
(* At some point will contain the running time*)
  end)
let report_run cmd r = Report_run.record cmd r

type cmp = { res : int; err:int ; ret:bool }
module Report_cmp=Make_Report(struct type t=cmp end)
let report_cmp = Report_cmp.record

let pretty_report fmt =
  Report_run.iter
    (fun test (run_result,time_result) ->
       Format.fprintf fmt
         "<testcase classname=%S name=%S time=\"%f\">%s</testcase>@."
         (Filename.basename (SubDir.get test.directory)) test.file time_result
         (let {res;err;ret} = Report_cmp.find test in
          Report_cmp.remove test;
          (if res=0 && err=0 && ret then "" else
             Format.sprintf "<failure type=\"Regression\">%s</failure>"
               (if not ret then Format.sprintf "Unexpected return code (returns %d instead of %d)" run_result test.exit_code
                else if res=1 then "Stdout oracle difference"
                else if res=2 then "Stdout System Error (missing oracle?)"
                else if err=1 then "Stderr oracle difference"
                else if err=2 then "Stderr System Error (missing oracle?)"
                else "Unexpected errror"))));
  (* Test that were compared but not runned *)
  Report_cmp.iter
    (fun test {res;err;ret} ->
       Format.fprintf fmt
         "<testcase classname=%S name=%S>%s</testcase>@."
         (Filename.basename (SubDir.get test.directory)) test.file
         (if res=0 && err=0 && ret  then "" else
            Format.sprintf "<failure type=\"Regression\">%s</failure>"
              (if not ret then "Unexpected return code"
               else if res=1 then "Stdout oracle difference"
               else if res=2 then "Stdout System Error (missing oracle?)"
               else if err=1 then "Stderr oracle difference"
               else if err=2 then "Stderr System Error (missing oracle?)"
               else "Unexpected errror")))

let xunit_report () =
  if !xunit then begin
    let out = open_out_bin "xunit.xml" in
    let fmt = Format.formatter_of_out_channel out in
    Format.fprintf fmt
      "<?xml version=\"1.0\" encoding=\"UTF-8\" ?>\
       @\n<testsuite errors=\"%d\" failures=\"%d\" name=\"%s\" tests=\"%d\" time=\"%f\" timestamp=\"%f\">\
       @\n%t</testsuite>@."
      (shared.summary_run-shared.summary_ret)
      (shared.summary_log-shared.summary_ok)
      "Frama-C"
      shared.summary_log
      ((Unix.times()).Unix.tms_cutime -. shared.summary_time)
      (Unix.gettimeofday ())
      pretty_report;
    close_out out;
  end


let do_command command =
  match command with
  | Toplevel command ->
    (* Update : copy the logs. Do not enqueue any cmp
       Run | Show: launch the command, then enqueue the cmp
       Gui: launch the command in the gui
       Examine : just enqueue the cmp *)
    if !behavior = Update
    then Cmd.update_toplevel_command command
    else begin
      (* Run, Show, Gui or Examine *)
      if !behavior = Gui then begin
        (* basic_command_string does not redirect the outputs, and does
           not overwrite the result files *)
        let basic_command_string = Cmd.basic_command_string command in
        lock_printf "%% launch GUI: %s@." basic_command_string ;
        ignore (launch basic_command_string)
      end
      else begin
        let command_string = Cmd.command_string command in
        let summary_ret =
          if !behavior <> Examine
          then begin
            if !verbosity >= 1
            then lock_printf "%% launch TOPLEVEL: %s@." command_string ;
            let launch_result = launch command_string in
            let time = 0. (* Individual time is difficult to compute correctly
                             for now, and currently unused *) in
            report_run command (launch_result, time) ;
            let summary_ret = launch_result = command.exit_code in
            if not summary_ret then
              lock_printf "%% Unexpected code (returns %d instead of %d) for command: %s@." launch_result command.exit_code command_string ;
            summary_ret
          end
          else false
        in
        lock ();
        if summary_ret then
          shared.summary_ret <- succ shared.summary_ret;
        shared.summary_run <- succ shared.summary_run ;
        Queue.push (Cmp_Toplevel (command,summary_ret)) shared.cmps;
        List.iter
          (fun log -> Queue.push (Cmp_Log (command.directory, command.file, log)) shared.cmps)
          command.log_files;
        unlock ()
      end
    end
  | Target (execnow, cmds) ->
    let continue res =
      lock();
      shared.summary_log <- succ shared.summary_log;
      if res = 0
      then begin
        shared.summary_ok <- succ shared.summary_ok;
        Queue.transfer shared.commands cmds;
        shared.commands <- cmds;
        shared.building_target <- false;
        Condition.broadcast shared.work_available;
        if !behavior = Examine || !behavior = Run
        then begin
          List.iter
            (fun log -> Queue.push (Cmp_Log(execnow.ex_dir, execnow.ex_file, log)) shared.cmps)
            execnow.ex_log
        end
      end
      else begin
        let rec treat_cmd = function
            Toplevel cmd ->
            shared.summary_run <- succ shared.summary_run;
            shared.summary_ret <- succ shared.summary_ret;
            Cmd.remove_results cmd;
          | Target (execnow,cmds) ->
            shared.summary_run <- succ shared.summary_run;
            shared.summary_ret <- succ shared.summary_ret;
            remove_execnow_results execnow;
            Queue.iter treat_cmd cmds
        in
        Queue.iter treat_cmd cmds;
        Queue.push (Target_error execnow) shared.diffs;
        shared.building_target <- false;
        Condition.signal shared.diff_available
      end;
      unlock()
    in

    if !behavior = Update then begin
      update_command command;
      lock ();
      shared.building_target <- false;
      Condition.signal shared.work_available;
      unlock ();
    end else
      begin
        if !behavior <> Examine && not (!(execnow.ex_done) && execnow.ex_once)
        then begin
          remove_execnow_results execnow;
          let cmd = execnow.ex_cmd in
          if !verbosity >= 1 || !behavior = Show then begin
            lock_printf "%% launch EXECNOW: %s@." cmd;
          end;
          shared.summary_run <- succ shared.summary_run;
          shared.summary_ret <- succ shared.summary_ret;
          let r = launch cmd in
          (* mark as already executed. For EXECNOW in test_config files,
             other instances (for example another test of the same
             directory), won't relaunch the command. For EXECNOW in
             stand-alone tests, there is only one copy of the EXECNOW
             anyway *)
          execnow.ex_done := true;
          continue r
        end
        else
          continue 0
      end

let log_ext = function Res -> ".res" | Err -> ".err"

let launch_and_check_compare_file diff ~cmp_string ~log_file ~oracle_file =
  lock();
  shared.summary_log <- shared.summary_log + 1;
  unlock();
  let res = if is_nonexisting_file log_file then 2 else launch cmp_string in
  begin
    match res with
      0 ->
      lock();
      shared.summary_ok <- shared.summary_ok + 1;
      unlock()
    | 1 ->
      lock();
      Queue.push diff shared.diffs;
      Condition.signal shared.diff_available;
      unlock()
    | 2 ->
      lock_printf
        "%% System error while comparing. Maybe one of the files is missing...@\n%s or %s@."
        log_file oracle_file
    | n ->
      lock_printf
        "%% Comparison function exited with code %d for files %s and %s. \
         Allowed exit codes are 0 (no diff), 1 (diff found) and \
         2 (system error). This is a fatal error.@." n log_file oracle_file;
      exit 2
  end;
  res

let check_file_is_empty_or_nonexisting diff ~log_file =
  if is_file_empty_or_nonexisting log_file then
    0
  else begin
    lock();
    (* signal that there's a problem. *)
    shared.summary_log <- shared.summary_log + 1;
    Queue.push diff shared.diffs;
    Condition.signal shared.diff_available;
    unlock();
    1
  end

(* Searches for executable [s] in the directories contained in the PATH
     environment variable. Returns [None] if not found, or
     [Some <fullpath>] otherwise. *)
let find_in_path =
  let path_separator = if Sys.os_type = "Win32" then ";" else ":" in
  let re_path_sep = Str.regexp path_separator in
  fun s ->
    let s = trim_right s in
    let path_dirs = str_split re_path_sep (Sys.getenv "PATH") in
    let found = ref "" in
    try
      List.iter (fun dir ->
          let fullname = dir ^ Filename.dir_sep ^ s in
          if Sys.file_exists fullname then begin
            found := fullname;
            raise Exit
          end
        ) path_dirs;
      None
    with Exit ->
      Some !found

(* filter commands are executed from the same directory than test commands *)
let get_filter_cmd = match !dune_mode with
  | 0 | 1 -> fun _ s -> dune_feature_cmd s
  | _ -> fun cmd s  -> Format.sprintf "(cd %s && (%s))"
      (SubDir.make_result_file cmd.directory "")
      (dune_feature_cmd s)

let get_unfiltered_log = match !dune_mode with
  | 0 | 1 -> fun s -> s
  | _ -> Filename.basename

let do_filter =
  let regexp_ptest_oracle = Str.regexp "@PTEST_ORACLE@" in
  fun cmd kind ->
    match cmd.filter with
    | None -> ()
    | Some filter ->
      let log_prefix = Cmd.log_prefix cmd in
      let log_ext = log_ext kind in
      let log_file = Filename.sanitize (log_prefix ^ log_ext ^ ".log") in
      let foracle = (Filename.basename log_prefix) ^ log_ext ^ ".oracle" in
      let filter = str_global_replace regexp_ptest_oracle foracle filter in
      let exec_name, params = command_partition filter in
      let exec_name =
        if Sys.file_exists exec_name || not (Filename.is_relative exec_name)
        then exec_name
        else
          match find_in_path exec_name with
          | Some full_exec_name -> full_exec_name
          | None -> (* must be in the suite directory *)
            Filename.concat
              (Cmd.get_ptest_dir cmd)
              (Filename.basename exec_name)
      in
      let filter_cmd =
        let unfiltered_file = Filename.sanitize (log_prefix ^ log_ext ^ ".unfiltered-log") in
        let unfiltered_log = get_unfiltered_log unfiltered_file in
        let filter_cmd = Format.sprintf "%s | %s%s"
            (* the filter command can be a diff from a [@PTEST_ORACLE@] *)
            (if Sys.file_exists unfiltered_file then "cat " ^ unfiltered_log else "echo \"\"")
            exec_name params
        in
        let filter_cmd = get_filter_cmd cmd filter_cmd in
        Format.sprintf "%s > %s 2> %s" filter_cmd log_file dev_null
      in
      if !verbosity >= 1
      then lock_printf "%% launch FILTER:@\n%s@." filter_cmd;
      ignore (launch filter_cmd)

let compare_one_file cmp log_prefix oracle_prefix log_kind =
  if !behavior = Show
  then begin
    lock();
    Queue.push (Command_error(cmp,log_kind)) shared.diffs;
    Condition.signal shared.diff_available;
    unlock();
    -1
  end else
    let ext = log_ext log_kind in
    let log_file = Filename.sanitize (log_prefix ^ ext ^ ".log") in
    let oracle_file = Filename.sanitize (oracle_prefix ^ ext ^ ".oracle") in
    do_filter cmp log_kind;
    if not (Sys.file_exists oracle_file) then
      check_file_is_empty_or_nonexisting (Command_error (cmp,log_kind)) ~log_file
    else begin
      let cmp_string = Format.sprintf "%s %s %s > %s 2> %s"
          !do_cmp log_file oracle_file dev_null dev_null
      in
      if !verbosity >= 2 then lock_printf "%% launch CMP (%d%s): %s@."
          cmp.n
          ext
          cmp_string;
      launch_and_check_compare_file (Command_error (cmp,log_kind))
        ~cmp_string ~log_file ~oracle_file
    end

let compare_one_log_file dir ~test_file ~log =
  if !behavior = Show
  then begin
    lock();
    Queue.push (Log_error(dir,test_file,log)) shared.diffs;
    Condition.signal shared.diff_available;
    unlock()
  end else
    let log_file = Filename.sanitize (SubDir.make_result_file dir log) in
    let oracle_file = Filename.sanitize (SubDir.make_oracle_file dir log) in
    let cmp_string = Format.sprintf "%s %s %s > %s 2> %s"
        !do_cmp  log_file oracle_file dev_null dev_null in
    if !verbosity >= 2 then lock_printf "%% launch CMP-LOG: %s/%s %s/%s@." (SubDir.get dir) log (SubDir.get dir) oracle_file;
    ignore (launch_and_check_compare_file (Log_error (dir,test_file,log))
              ~cmp_string ~log_file ~oracle_file)

let do_cmp = function
  | Cmp_Toplevel (cmd,ret) ->
    let log_prefix = Cmd.log_prefix cmd in
    let oracle_prefix = Cmd.oracle_prefix cmd in
    let cmp = { res = compare_one_file cmd log_prefix oracle_prefix Res;
                err = compare_one_file cmd log_prefix oracle_prefix Err;
                ret
              }
    in
    report_cmp cmd cmp
  | Cmp_Log(dir, test_file, log) ->
    ignore (compare_one_log_file dir ~test_file ~log)

let worker_thread () =
  while true do
    lock () ;
    if (Queue.length shared.commands) + (Queue.length shared.cmps) < !n
    then Condition.signal shared.commands_empty;
    try
      let cmp = Queue.pop shared.cmps in
      unlock () ;
      do_cmp cmp
    with Queue.Empty ->
    try
      let rec real_command () =
        let command =
          try
            if shared.building_target then raise Queue.Empty;
            Queue.pop shared.target_queue
          with Queue.Empty ->
            Queue.pop shared.commands
        in
        match command with
          Target _ ->
          if shared.building_target
          then begin
            Queue.push command shared.target_queue;
            real_command()
          end
          else begin
            shared.building_target <- true;
            command
          end
        | _ -> command
      in
      let command = real_command() in
      unlock () ;
      do_command command
    with Queue.Empty ->
      if shared.commands_finished
      && Queue.is_empty shared.target_queue
      && not shared.building_target
      (* a target being built would mean work can still appear *)

      then (unlock () ; Thread.exit ());

      Condition.signal shared.commands_empty;
      (* we still have the lock at this point *)

      Condition.wait shared.work_available shared.lock;
      (* this atomically releases the lock and suspends
         the thread on the condition work_available *)

      unlock ();
  done

let diff_check_exist old_file new_file =
  if Sys.file_exists old_file then begin
    if Sys.file_exists new_file then begin
      !do_diffs ^ " " ^ old_file ^ " " ^ new_file
    end else begin
      "echo \"+++ " ^ new_file ^ " does not exist. Showing " ^
      old_file ^ "\";" ^ " cat " ^ old_file
    end
  end else begin
    "echo \"--- " ^ old_file ^ " does not exist. Showing " ^
    new_file ^ "\";" ^ " cat " ^ new_file
  end

let do_diff =
  let stdout_redir_regexp = Str.regexp "[^2]> ?\\([-a-zA-Z0-9_/.]+\\)"
  and stderr_redir_regexp = Str.regexp "2> ?\\([-a-zA-Z0-9_/.]+\\)";
  in
  function
  | Command_error (diff, kind) ->
    let log_prefix = Cmd.log_prefix diff in
    let log_ext = log_ext kind in
    let log_file = Filename.sanitize (log_prefix ^ log_ext ^ ".log") in
    do_filter diff kind ;
    let test_file = SubDir.make_file diff.directory diff.file in
    lock_printf "#------ Oracle difference for test file: %s@.%t@." test_file print_default_env ;
    if !behavior = Show
    then ignore (launch ("cat " ^ log_file))
    else
      let oracle_prefix = Cmd.oracle_prefix diff in
      let oracle_file =
        Filename.sanitize (oracle_prefix ^ log_ext ^ ".oracle")
      in
      let diff_string = diff_check_exist oracle_file log_file in
      if !verbosity >= 2 then lock_printf "%% launch DIFF (%d%s): %s@."
          diff.n
          log_ext
          diff_string;
      ignore (launch diff_string);
      lock_printf "#- Tested file: %s #- Command:@\n%s@." test_file (Cmd.command_string diff);
  | Target_error execnow ->
    let test_file = SubDir.make_file execnow.ex_dir execnow.ex_file in
    lock_printf "#------ Custom command failed for test file %s:@\n" test_file;
    let print_redirected out redir_regexp =
      try
        Mutex.lock str_mutex;
        ignore (Str.search_forward redir_regexp execnow.ex_cmd 0);
        let file = Str.matched_group 1 execnow.ex_cmd in
        Mutex.unlock str_mutex;
        lock_printf "#- %s redirected to %s:@\n" out file;
        if not (Sys.file_exists file) then
          lock_printf "#- error: file does not exist: %s:@\n" file
        else
          ignore (launch ("cat " ^ file));
      with Not_found -> lock_printf "#- error: EXECNOW command without %s redirection: %s@\n" out execnow.ex_cmd
    in
    print_redirected "stdout" stdout_redir_regexp;
    print_redirected "stderr" stderr_redir_regexp;
    lock_printf "#- Tested file: %s #- Custom command: %s@\n" test_file execnow.ex_cmd;
  | Log_error(dir, test_file, log) ->
    let test_file = SubDir.make_file dir test_file in
    lock_printf "#------ Log difference for test file: %s@." test_file ;
    let result_file =
      Filename.sanitize (SubDir.make_result_file dir log)
    in
    if !behavior = Show
    then ignore (launch ("cat " ^ result_file))
    else begin
      let oracle_file =
        Filename.sanitize (SubDir.make_oracle_file dir log)
      in
      let diff_string = diff_check_exist oracle_file result_file in
      if !verbosity >= 2 then lock_printf "%% launch DIFF-LOG: %s@."
          diff_string;
      ignore (launch diff_string)
    end;
    lock_printf "#- Tested file: %s #- Log file: %s@." test_file result_file

let diff_thread () =
  lock () ;
  while true do
    try
      let diff = Queue.pop shared.diffs in
      unlock ();
      do_diff diff;
      lock ()
    with Queue.Empty ->
      if shared.cmp_finished then (unlock () ; Thread.exit ());

      Condition.wait shared.diff_available shared.lock
      (* this atomically releases the lock and suspends
         the thread on the condition cmp_available *)
  done

let test_pattern config =
  let regexp = Str.regexp config.dc_test_regexp in
  fun file -> str_string_match regexp file 0

let files = Queue.create ()

(* if we have some references to directories in the default config, they
   need to be adapted to the actual test directory. *)
let update_dir_ref dir config =
  let update_execnow e = { e with ex_dir = dir } in
  let dc_execnow = List.map update_execnow config.dc_execnow in
  { config with dc_execnow }

let () =
  (* enqueue the test files *)
  let default_suites () =
    let priority = "tests/idct" in
    let default = !default_suites in
    if List.mem priority default
    then priority :: (List.filter (fun name -> name <> priority) default)
    else default
  in
  let suites =
    match !suites with
    | [] -> default_suites ()
    | l ->
      List.fold_left (fun acc x ->
          if x = "tests"
          then (default_suites ()) @ acc
          else x::acc
        ) [] l
  in
  let interpret_as_file suite =
    try
      let ext = Filename.chop_extension suite in
      ext <> ""
    with Invalid_argument _ -> false
  in
  let exclude_suite, exclude_file =
    List.fold_left
      (fun (suite,test) x ->
         if interpret_as_file x then (suite,x::test) else (x::suite,test))
      ([],[]) !exclude_suites
  in
  List.iter
    (fun suite ->
       if !verbosity >= 2 then lock_printf "%% producer now treating test %s\n%!" suite;
       (* the "suite" may be a directory or a single file *)
       let interpret_as_file = interpret_as_file suite in
       let directory =
         SubDir.create (if interpret_as_file
                        then
                          Filename.dirname suite
                        else
                          suite)
       in
       let file = SubDir.make_file directory dir_config_file in
       let dir_config = Test_config.current_config () in
       let dir_config = update_dir_ref directory dir_config in
       let dir_config =
         if Sys.file_exists file
         then begin
           let scan_buffer = Scanf.Scanning.from_file file in
           Test_config.scan_directives ~drop:false directory
             ~file scan_buffer dir_config
         end
         else dir_config
       in
       let process_dir action =
         let dirname = SubDir.get directory in
         let dir_files = Array.to_list (Sys.readdir dirname) in
         (* ignore hidden files (starting with '.') *)
         let dir_files =
           List.filter (fun n -> String.get n 0 <> '.') dir_files
         in
         if !verbosity >= 2 then
           lock_printf "%% - Look at %d entries of the directory %S ...@."
             (List.length dir_files) dirname;
         List.iter
           (fun file ->
              (* creates a symbolic link into the result directory *)
              mk_symbolic_link directory file ;
              assert (Filename.is_relative file);
              action file) dir_files
       in
       if interpret_as_file then begin
         if not (List.mem suite exclude_file) then begin
           process_dir (fun _ -> ()) ;
           Queue.push (Filename.basename suite, directory, dir_config) files
         end;
       end
       else begin
         if not (List.mem suite exclude_suite) then
           process_dir
             (fun file ->
                if test_pattern dir_config file &&
                   (not (List.mem (SubDir.make_file directory file) exclude_file))
                then
                  Queue.push (file, directory, dir_config) files;
             );
       end)
    suites

let dispatcher () =
  try
    while true
    do
      lock ();
      while (Queue.length shared.commands) + (Queue.length shared.cmps) >= !n
      do
        Condition.wait shared.commands_empty shared.lock;
      done;
      (* we have the lock *)
      let file, directory, config = Queue.pop files in
      if !verbosity >= 2 then lock_printf "%% - Process test file %s ...@." file;
      let config =
        Test_config.scan_test_file config directory file in
      let nb_files = List.length config.dc_commands in
      let make_toplevel_cmd =
        let i = ref 0 in
        fun {toplevel; make_cmd; opts=options; logs=log_files; macros; exit_code; timeout} ->
          let n = !i in
          incr i;
          Cmd.expand_macros ~execnow:false ~defaults:config.dc_macros
            { file; make_cmd;  options; toplevel; nb_files; directory; n; log_files;
              filter = config.dc_filter; macros;
              exit_code = begin
                match exit_code with
                | None -> 0
                | Some exit_code ->
                  try int_of_string exit_code with
                  | _ -> lock_eprintf "@[%s: integer required for directive EXIT: %s (defaults to 0)@]@." file exit_code ; 0
              end;
              execnow=false;
              timeout;
            }
      in
      let nb_files_execnow = List.length config.dc_execnow in
      let make_execnow_cmd =
        let e = ref 0 in
        fun execnow ->
          let n = !e in
          incr e;
          let cmd = Cmd.expand_macros ~execnow:true ~defaults:config.dc_macros
              {file ;
               nb_files = nb_files_execnow;
               log_files = execnow.ex_log;
               options = "";
               toplevel = execnow.ex_cmd;
               make_cmd = execnow.ex_make_cmd;
               exit_code = 0;
               n;
               directory;
               filter = None; (* No filter for execnow command *)
               macros = execnow.ex_macros;
               execnow = true;
               timeout = execnow.ex_timeout;
              }
          in
          let process_macros s = Macros.expand cmd.macros s in
          { ex_cmd = Cmd.basic_command_string cmd;
            ex_make_cmd = execnow.ex_make_cmd;
            ex_macros = cmd.macros;
            ex_log = cmd.log_files;
            ex_bin = List.map process_macros execnow.ex_bin;
            ex_dir = execnow.ex_dir;
            ex_file = cmd.file;
            ex_once = execnow.ex_once;
            ex_done = execnow.ex_done;
            ex_timeout = cmd.timeout;
          }
      in
      let treat_option q cmd =
        Queue.push
          (Toplevel (make_toplevel_cmd cmd))
          q;
      in
      if not config.dc_dont_run
      then begin
        (match config.dc_execnow with
         | hd :: tl ->
           let subworkqueue = Queue.create () in
           List.iter (treat_option subworkqueue) config.dc_commands;
           let target =
             List.fold_left
               (fun current_target execnow ->
                  let subworkqueue = Queue.create () in
                  Queue.add current_target subworkqueue;
                  Target(make_execnow_cmd execnow,subworkqueue))
               (Target(make_execnow_cmd hd,subworkqueue)) tl
           in
           Queue.push target shared.commands
         | [] ->
           List.iter
             (treat_option shared.commands)
             config.dc_commands);
        Condition.broadcast shared.work_available;
      end;
      unlock () ;
    done
  with Queue.Empty ->
    shared.commands_finished <- true;
    unlock ()

let () =
  let worker_ids = Array.init !n
      (fun _ -> Thread.create worker_thread ())
  in
  let diff_id = Thread.create diff_thread () in

  dispatcher ();
  if !behavior = Run
  then
    lock_printf "%% Dispatch finished, waiting for workers to complete@.";
  ignore (Thread.create
            (fun () ->
               while true do
                 Condition.broadcast shared.work_available;
                 Thread.delay 0.5;
               done)
            ());
  Array.iter Thread.join worker_ids;

  if !behavior = Run
  then
    lock_printf "%% Comparisons finished, waiting for diffs to complete@.";
  lock();
  shared.cmp_finished <- true;
  unlock();
  ignore (Thread.create
            (fun () ->
               while true do
                 Condition.broadcast shared.diff_available;
                 Thread.delay 0.5;
               done)
            ());
  Thread.join diff_id;
  if !behavior = Run
  then
    lock_printf "%% Diffs finished. Summary:@\nRun  = %d of %d@\nOk   = %d of %d@\nTime = %f s.@."
      shared.summary_ret shared.summary_run shared.summary_ok shared.summary_log
      ((Unix.times()).Unix.tms_cutime -. shared.summary_time);
  xunit_report ();
  let error_code =
    if !do_error_code && ((shared.summary_log <> shared.summary_ok) || (shared.summary_ret <> shared.summary_run))
    then 1
    else 0
  in
  exit error_code

(*
Local Variables:
compile-command: "LC_ALL=C make -C .. ptests"
End:
*)
