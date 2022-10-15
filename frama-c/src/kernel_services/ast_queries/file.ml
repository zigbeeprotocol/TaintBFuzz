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

open Cil_types
open Cil
open Visitor
open Cil_datatype

type cpp_opt_kind = Gnu | Not_gnu | Unknown

let pretty_cpp_opt_kind fmt =
  function
  | Gnu -> Format.pp_print_string fmt "Gnu"
  | Not_gnu -> Format.pp_print_string fmt "Not_gnu"
  | Unknown -> Format.pp_print_string fmt "Unknown"

type file =
  | NeedCPP of
      Filepath.Normalized.t (* Filename of the [.c] to preprocess. *)
      * string (* Preprocessing command, as given by -cpp-command, or
                  the default value, but without extra arguments. *)
      * string list (* Extra arguments, specific to this file (that is,
                       obtained via a JCDB, or -cpp-extra-args-per-file,
                       but _not_ those via -cpp-extra-args), to be given
                       to the C preprocessor. *)
      * cpp_opt_kind (* Whether the preprocessor is known to be compatible with
                        GCC-style options (mostly, -D and -I). *)
  | NoCPP of Filepath.Normalized.t (** filename of a preprocessed [.c] *)
  | External of Filepath.Normalized.t * string
  (* file * name of plug-in that handles it *)

module D =
  Datatype.Make
    (struct
      include Datatype.Serializable_undefined
      type t = file
      let name = "File"
      let reprs =
        [ NeedCPP(Filepath.Normalized.empty, "", [], Unknown);
          NoCPP Filepath.Normalized.empty;
          External(Filepath.Normalized.empty, "")
        ]
      let structural_descr = Structural_descr.t_abstract
      let mem_project = Datatype.never_any_project
      let copy = Datatype.identity (* immutable strings *)
      let internal_pretty_code p_caller fmt t =
        let pp fmt = match t with
          | NoCPP s ->
            Format.fprintf fmt "@[File.NoCPP %a@]" Filepath.Normalized.pretty s
          | External (f,p) ->
            Format.fprintf fmt "@[File.External (%a,%S)@]"
              Filepath.Normalized.pretty f p
          | NeedCPP (f,cmd,extra,kind) ->
            Format.fprintf
              fmt "@[File.NeedCPP (%a,%S,%S,%a)@]"
              Filepath.Normalized.pretty f
              cmd
              (String.concat " " extra)
              pretty_cpp_opt_kind kind
        in
        Type.par p_caller Type.Call fmt pp
    end)
include D

let check_suffixes = Hashtbl.create 17
let new_file_type = Hashtbl.add check_suffixes
let get_suffixes () =
  Hashtbl.fold
    (fun s _ acc -> s :: acc)
    check_suffixes
    [ ".c"; ".i"; ".h" ]

let get_filepath = function NeedCPP (s, _, _, _) | NoCPP s | External (s, _) -> s
let get_name s = Filepath.Normalized.to_pretty_string (get_filepath s)

(* ************************************************************************* *)
(** {2 Preprocessor command} *)
(* ************************************************************************* *)

(* Do not trust custom command-line to be gnu like by default, but give
   them a chance, with a warning indicating that things may go wrong. *)
let cpp_opt_kind () =
  if Kernel.CppGnuLike.is_set () then
    if Kernel.CppGnuLike.get () then Gnu else Not_gnu
  else Unknown

let is_cpp_gnu_like () =
  let open Fc_config in
  let cpp_cmd = Kernel.CppCommand.get () in
  match cpp_cmd = "", using_default_cpp, preprocessor_is_gnu_like with
  | true, true, true -> Gnu
  | true, true, false -> Not_gnu
  | _, _, _ -> cpp_opt_kind ()

(* the preprocessor command is:
   If the program has an explicit argument -cpp-command "XX -Y"
   (quotes are required by the shell)
   then XX -Y
   else use the command in [Fc_config.preprocessor].*)
let get_preprocessor_command () =
  let cmdline = Kernel.CppCommand.get() in
  if cmdline <> "" then cmdline else Fc_config.preprocessor

let from_filename ?cpp f =
  let cpp =
    let cpp_command = Kernel.CppCommand.get() in
    if cpp_command <> "" then cpp_command
    else if cpp = None then get_preprocessor_command ()
    else Option.get cpp
  in
  let extra_for_this_file =
    let extra_by_file =
      try Kernel.CppExtraArgsPerFile.find f
      with Not_found -> ""
    in
    let jcdb_flags = Json_compilation_database.get_flags f in
    if extra_by_file <> "" && jcdb_flags <> [] then
      Kernel.warning ~wkey:Kernel.wkey_jcdb
        "found flags for file %a@ both in -cpp-extra-args-per-file and@ \
         in the json compilation database;@ the latter will be ignored"
        Filepath.Normalized.pretty f;
    if extra_by_file <> "" then [extra_by_file] else jcdb_flags
  in
  if Filename.check_suffix (f:>string) ".i" then begin
    NoCPP f
  end else
    let suf =
      try
        let suf_idx = String.rindex (f:>string) '.' in
        String.sub (f:>string) suf_idx (String.length (f:>string) - suf_idx)
      with Not_found -> (* raised by String.rindex if '.' \notin f *)
        ""
    in
    if Hashtbl.mem check_suffixes suf then
      External (f, suf)
    else if cpp <> "" then begin
      if not Fc_config.preprocessor_keep_comments then
        Kernel.warning ~once:true
          "Default pre-processor does not keep comments. Any ACSL annotation \
           on non-pre-processed file will be discarded.";
      NeedCPP (f, cpp, extra_for_this_file, is_cpp_gnu_like ())
    end else
      Kernel.abort "No working pre-processor found. You can only analyze \
                    pre-processed .i files."

(* ************************************************************************* *)
(** {2 Internal states} *)
(* ************************************************************************* *)

module Files : sig
  val get: unit -> t list
  val register: t list -> unit
  val pre_register: t -> unit
  val is_computed: unit -> bool
  val reset: unit -> unit
  val pre_register_state: State.t
end = struct

  module S =
    State_builder.List_ref
      (D)
      (struct
        let dependencies =
          [ Kernel.CppCommand.self;
            Kernel.CppExtraArgs.self;
            Kernel.CppExtraArgsPerFile.self;
            Kernel.JsonCompilationDatabase.self;
            Kernel.Files.self ]
        let name = "Files for preprocessing"
      end)

  module Pre_files =
    State_builder.List_ref
      (D)
      (struct
        let dependencies = []
        let name = "Built-ins headers and source"
      end)

  let () =
    State_dependency_graph.add_dependencies
      ~from:S.self
      [ Ast.self; Ast.UntypedFiles.self; Cabshelper.Comments.self ]

  let () =
    State_dependency_graph.add_dependencies
      ~from:Pre_files.self
      [ Ast.self;
        Ast.UntypedFiles.self;
        Cabshelper.Comments.self;
        Cil_builtins.Frama_c_builtins.self ]

  let () =
    Ast.add_linked_state Cabshelper.Comments.self

  let pre_register_state = Pre_files.self

  (* Allow to register files in advance, e.g. prolog files for plugins *)
  let pre_register file =
    let prev_files = Pre_files.get () in Pre_files.set (prev_files @ [file])

  let register files =
    if S.is_computed () then
      raise (Ast.Bad_Initialization "[File.register] Too many initializations");
    let prev_files = S.get () in
    S.set (prev_files @ files);
    S.mark_as_computed ()

  let get () = Pre_files.get () @ S.get ()
  let is_computed () = S.is_computed ()

  let reset () =
    let selection = State_selection.with_dependencies S.self in
    (* Keep built-in files set *)
    Project.clear ~selection ()
end

let get_all = Files.get
let pre_register = Files.pre_register


(* ************************************************************************* *)
(** {2 Machdep} *)
(* ************************************************************************* *)

(* not exported, see [pretty_machdep] below. *)
let print_machdep fmt (m : Cil_types.mach) =
  begin
    let open Cil_types in
    Format.fprintf fmt "Machine: %s@\n" m.version ;
    let pp_size_error fmt v =
      if v < 0
      then Format.pp_print_string fmt "error"
      else Format.fprintf fmt "%2d" v
    in
    let pp_size_bits fmt v =
      if v >= 0 then Format.fprintf fmt "%d bits, " (v*8)
    in
    let pp_align_error fmt v =
      if v < 0
      then Format.pp_print_string fmt "alignof error"
      else Format.fprintf fmt "aligned on %d bits" (v*8)
    in
    List.iter
      (fun (name,size,align) ->
         Format.fprintf fmt
           "   sizeof %11s = %a (%a%a)@\n"
           name pp_size_error size pp_size_bits size pp_align_error align)
      [
        "short",  m.sizeof_short, m.alignof_short ;
        "int",    m.sizeof_int,   m.alignof_int ;
        "long",   m.sizeof_long,  m.alignof_long ;
        "long long", m.sizeof_longlong,  m.alignof_longlong ;
        "float",  m.sizeof_float,  m.alignof_float ;
        "double", m.sizeof_double, m.alignof_double ;
        "long double", m.sizeof_longdouble, m.alignof_longdouble ;
        "pointer", m.sizeof_ptr, m.alignof_ptr ;
        "void", m.sizeof_void, m.sizeof_void ;
        "function", m.sizeof_fun, m.alignof_fun ;
      ] ;
    List.iter
      (fun (name,typeof) ->
         Format.fprintf fmt "   typeof %11s = %s@\n" name typeof)
      [
        "sizeof(T)", m.size_t ;
        "wchar_t", m.wchar_t ;
        "ptrdiff_t", m.ptrdiff_t ;
      ] ;
    Format.fprintf fmt "   char is %s@\n"
      (if m.char_is_unsigned then "unsigned" else "signed");
    Format.fprintf fmt "   machine is %s endian@\n"
      (if m.little_endian then "little" else "big") ;
    Format.fprintf fmt "   strings are %s chars@\n"
      (if m.const_string_literals then "const" else "writable") ;
    Format.fprintf fmt "   assembly names %s leading '_'@\n"
      (if m.underscore_name then "have" else "have no") ;
    Format.fprintf fmt "   compiler %s builtin __va_list@\n"
      (if m.has__builtin_va_list then "has" else "has not") ;
  end

module DatatypeMachdep = Datatype.Make_with_collections(struct
    include Datatype.Serializable_undefined
    let reprs = [Machdeps.x86_32]
    let name = "File.Machdep"
    type t = Cil_types.mach
    let compare : t -> t -> int = Stdlib.compare
    let equal : t -> t -> bool = (=)
    let hash : t -> int = Hashtbl.hash
    let copy = Datatype.identity
  end)

let default_machdeps =
  [ "x86_16", Machdeps.x86_16;
    "x86_32", Machdeps.x86_32;
    "x86_64", Machdeps.x86_64;
    "gcc_x86_16", Machdeps.gcc_x86_16;
    "gcc_x86_32", Machdeps.gcc_x86_32;
    "gcc_x86_64", Machdeps.gcc_x86_64;
    "ppc_32", Machdeps.ppc_32;
    "msvc_x86_64", Machdeps.msvc_x86_64;
  ]

let regexp_existing_machdep_macro = Str.regexp "-D[ ]*__FC_MACHDEP_"

let existing_machdep_macro () =
  let extra = String.concat " " (Kernel.CppExtraArgs.get ()) in
  try
    ignore (Str.search_forward regexp_existing_machdep_macro extra 0);
    true
  with Not_found -> false

let machdep_macro = function
  | "x86_16"                -> "__FC_MACHDEP_X86_16"
  | "gcc_x86_16"            -> "__FC_MACHDEP_GCC_X86_16"
  | "x86_32"                -> "__FC_MACHDEP_X86_32"
  | "gcc_x86_32"            -> "__FC_MACHDEP_GCC_X86_32"
  | "x86_64"                -> "__FC_MACHDEP_X86_64"
  | "gcc_x86_64"            -> "__FC_MACHDEP_GCC_X86_64"
  | "ppc_32"                -> "__FC_MACHDEP_PPC_32"
  | "msvc_x86_64"           -> "__FC_MACHDEP_MSVC_X86_64"
  | s ->
    let res = "__FC_MACHDEP_" ^ (String.uppercase_ascii s) in
    Kernel.warning ~once:true
      "machdep %s has no registered macro. Using %s for pre-processing" s res;
    res

module Machdeps =
  State_builder.Hashtbl(Datatype.String.Hashtbl)(DatatypeMachdep)
    (struct
      let name = " File.Machdeps"
      let size = 5
      let dependencies = []
    end)

let mem_machdep s = Machdeps.mem s || List.mem_assoc s default_machdeps

let new_machdep s m =
  try
    let cm = Machdeps.find s in
    if not (cm = m) then
      Kernel.abort "trying to register incompatible machdeps under name `%s'" s
  with Not_found ->
    Machdeps.add s m

let pretty_machdeps fmt =
  Machdeps.iter (fun x _ -> Format.fprintf fmt "@ %s" x);
  List.iter (fun (x, _) -> Format.fprintf fmt "@ %s" x) default_machdeps

let machdep_help () =
  let m = Kernel.Machdep.get () in
  if m = "help" then begin
    Kernel.feedback
      "@[supported machines are%t@ (default is x86_64).@]"
      pretty_machdeps;
    raise Cmdline.Exit
  end else
    Cmdline.nop

let () = Cmdline.run_after_exiting_stage machdep_help

let set_machdep () =
  let m = Kernel.Machdep.get () in
  if not (mem_machdep m) then
    Kernel.abort "@[unsupported machine %s.@ Try one of%t.@]" m pretty_machdeps

let () = Cmdline.run_after_configuring_stage set_machdep

(* Local to this module. Use Cil.theMachine.theMachine outside *)
let get_machdep () =
  let m = Kernel.Machdep.get () in
  try
    Machdeps.find m
  with Not_found ->
  try
    List.assoc m default_machdeps
  with Not_found -> (* Should not happen given the checks above *)
    Kernel.fatal "Machdep %s not registered" m

let list_available_machdeps () =
  Machdeps.fold (fun m _ acc -> m :: acc) (List.map fst default_machdeps)

let pretty_machdep ?fmt ?machdep () =
  let machine = match machdep with None -> get_machdep () | Some m -> m in
  match fmt with
  | None -> Log.print_on_output (fun fmt -> print_machdep fmt machine)
  | Some fmt -> print_machdep fmt machine

(* ************************************************************************* *)
(** {2 Initializations} *)
(* ************************************************************************* *)

let create_temp_file ?debug name suffix =
  let of_string = Filepath.Normalized.of_string in
  try of_string (Extlib.temp_file_cleanup_at_exit ?debug name suffix)
  with Extlib.Temp_file_error s ->
    Kernel.abort "cannot create temporary file: %s" s

let safe_remove_file (f : Datatype.Filepath.t) =
  if not (Kernel.is_debug_key_enabled Kernel.dkey_parser) then
    Extlib.safe_remove (f :> string)

let replace_in_cpp_cmd cmdl supp_args in_file out_file =
  (* using Filename.quote for filenames which contain space or shell
     metacharacters *)
  let in_file = Filename.quote in_file
  and out_file = Filename.quote out_file in
  let substitute s =
    match Str.matched_string s with
    | "%%" -> "%"
    | "%args" -> supp_args
    | "%1" | "%i" | "%input" -> in_file
    | "%2" | "%o" | "%output" -> out_file
    | s -> s (* Unrecognized parameters are left intact *)
  in
  let regexp = Str.regexp "%%\\|%[a-z0-9]+" in
  try
    ignore (Str.search_forward regexp cmdl 0); (* Try to find one match *)
    Str.global_substitute regexp substitute cmdl
  with Not_found ->
    Format.sprintf "%s %s %s -o %s" cmdl supp_args in_file out_file

(* Note: using Pretty_utils.pp_list without forcing '~pre' and '~suf' to
   be empty strings can lead to issues when the commands are too long and
   Format's pretty-printer decides to insert newlines.
   This concatenation function serves as a reminder to avoid using them.
*)
let concat_strs ?(pre="") ?(sep=" ") l =
  if l = [] then ""
  else pre ^ (String.concat sep l)

let adjust_pwd fp cpp_command =
  if Kernel.JsonCompilationDatabase.is_set () then
    let cwd = Filepath.pwd () in
    let dir =
      match Json_compilation_database.get_dir fp with
      | None -> cwd
      | Some d -> (d:>string)
    in
    if cwd <> dir then Some dir, "cd " ^ dir ^ " && " ^ cpp_command
    else None, cpp_command
  else None, cpp_command

let build_cpp_cmd = function
  | NoCPP _ | External _ -> None
  | NeedCPP (f, cmdl, extra_for_this_file, is_gnu_like) ->
    if not (Sys.file_exists (f :> string)) then
      Kernel.abort "source file %a does not exist"
        Filepath.Normalized.pretty f;
    let debug = Kernel.is_debug_key_enabled Kernel.dkey_parser in
    let add_if_gnu opt =
      match is_gnu_like with
      | Gnu -> [opt]
      | Not_gnu -> []
      | Unknown ->
        Kernel.warning
          ~once:true
          "your preprocessor is not known to handle option `%s'. \
           If pre-processing fails because of it, please add \
           -no-cpp-frama-c-compliant option to Frama-C's command-line. \
           If you do not want to see this warning again, explicitly use \
           option -cpp-frama-c-compliant."
          opt;
        [opt]
    in
    let ppf = create_temp_file ~debug (Filename.basename (f :> string)) ".i" in
    (* Hypothesis: the preprocessor is POSIX compliant,
       hence understands -I and -D. *)
    let fc_include_args =
      if Kernel.FramaCStdLib.get () then [(Fc_config.framac_libc:>string)]
      else []
    in
    let fc_define_args =
      if not (existing_machdep_macro ())
      then [machdep_macro (Kernel.Machdep.get ())]
      else []
    in
    let fc_define_args = "__FRAMAC__" :: fc_define_args in
    (* Hypothesis: the preprocessor does support the arch-related
       options tested when 'configure' was run. *)
    let required_cpp_arch_args = (get_machdep ()).cpp_arch_flags in
    let supported_cpp_arch_args, unsupported_cpp_arch_args =
      List.partition (fun arg ->
          List.mem arg Fc_config.preprocessor_supported_arch_options)
        required_cpp_arch_args
    in
    if is_gnu_like = Unknown && not (Kernel.CppCommand.is_set ())
       && unsupported_cpp_arch_args <> [] then
      Kernel.warning ~once:true
        "your preprocessor is not known to handle option(s) `%s', \
         considered necessary for machdep `%s'. To ensure compatibility \
         between your preprocessor and the machdep, consider using \
         -cpp-command with the appropriate flags. \
         Your preprocessor is known to support these flags: %s"
        (concat_strs unsupported_cpp_arch_args) (Kernel.Machdep.get ())
        (concat_strs Fc_config.preprocessor_supported_arch_options);
    let nostdinc_arg =
      if Kernel.FramaCStdLib.get() then add_if_gnu "-nostdinc"
      else []
    in
    let output_defines_arg =
      let open Kernel in
      match ReadAnnot.get (), PreprocessAnnot.is_set (), PreprocessAnnot.get () with
      | true, true, true -> ["-dD"] (* keep '#defines' in preprocessed output *)
      | true, true, false -> []
      | true, false, _ -> add_if_gnu "-dD"
      | _, _, _ -> []
    in
    let gnu_implicit_args = output_defines_arg @ nostdinc_arg in
    let string_of_supp_args extra includes defines =
      Format.asprintf "%s%s%s"
        (concat_strs ~pre:"-I" ~sep:" -I" includes)
        (concat_strs ~pre:" -D" ~sep:" -D" defines)
        (concat_strs ~pre:" " ~sep:" " extra)
    in
    let supp_args =
      string_of_supp_args
        (gnu_implicit_args @ supported_cpp_arch_args @
         extra_for_this_file @ (Kernel.CppExtraArgs.get ()))
        fc_include_args fc_define_args
    in
    let cpp_command =
      replace_in_cpp_cmd cmdl supp_args (f:>string) (ppf:>string)
    in
    let workdir, cpp_command_with_chdir = adjust_pwd f cpp_command in
    if workdir <> None then
      Parse_env.set_workdir ppf (Option.get workdir);
    Kernel.feedback ~dkey:Kernel.dkey_pp
      "preprocessing with \"%s\""
      cpp_command_with_chdir;
    Some (cpp_command_with_chdir, ppf, supported_cpp_arch_args)

let abort_with_detailed_pp_message f cpp_command =
  let possible_cause =
    if Kernel.JsonCompilationDatabase.is_set () then
      if not (Json_compilation_database.has_entry f) then
        Format.asprintf "note: %s is set but \
                         contains no entries for '%a'.@ "
          Kernel.JsonCompilationDatabase.option_name
          Datatype.Filepath.pretty f
      else ""
    else
    if not (Kernel.CppExtraArgs.is_set ()) &&
       not (Kernel.CppExtraArgsPerFile.is_set ()) &&
       not (Kernel.CppCommand.is_set ()) then
      Format.asprintf
        "this is possibly due to missing preprocessor flags;@ \
         consider options %s, %s or %s.@ "
        Kernel.CppExtraArgs.option_name
        Kernel.JsonCompilationDatabase.option_name
        Kernel.CppCommand.option_name
    else ""
  in
  Kernel.abort
    "failed to run: %s\n(PWD: %s)@\n\
     %sSee chapter \"Preparing the Sources\" in the Frama-C user manual \
     for more details."
    cpp_command (Filepath.pwd ()) possible_cause

let parse_cabs cpp_command = function
  | NoCPP f ->
    if not (Sys.file_exists (f:>string)) then
      Kernel.abort "preprocessed file %a does not exist"
        Filepath.Normalized.pretty f;
    Kernel.feedback "Parsing %a (no preprocessing)"
      Datatype.Filepath.pretty f;
    Frontc.parse f ()
  | NeedCPP (f, cmdl, _extra_for_this_file, is_gnu_like) ->
    let cpp_command, ppf, logic_pp_args = Option.get cpp_command in
    Kernel.feedback "Parsing %a (with preprocessing)"
      Datatype.Filepath.pretty f;
    if Sys.command cpp_command <> 0 then begin
      safe_remove_file ppf;
      abort_with_detailed_pp_message f cpp_command
    end;
    let ppf =
      if Kernel.ReadAnnot.get() &&
         ((Kernel.PreprocessAnnot.is_set () &&
           Kernel.PreprocessAnnot.get())
          || (match is_gnu_like with
              | Gnu -> true
              | Not_gnu -> false
              | Unknown ->
                Kernel.warning
                  ~once:true
                  "trying to preprocess annotation with an unknown \
                   preprocessor."; true))
      then begin
        let supp_args =
          Format.asprintf "%s" (concat_strs ~pre:" " ~sep:" " logic_pp_args)
        in
        let ppf' =
          try Logic_preprocess.file ".c"
                (replace_in_cpp_cmd cmdl supp_args)
                (ppf : Filepath.Normalized.t :> string)
          with Sys_error _ as e ->
            safe_remove_file ppf;
            Kernel.abort "preprocessing of annotations failed (%s)"
              (Printexc.to_string e)
        in
        safe_remove_file ppf ;
        ppf'
      end else ppf
    in
    let (cil,(_,defs)) = Frontc.parse ppf () in
    cil.fileName <- f;
    safe_remove_file ppf;
    (cil,(f,defs))
  | External (f,suf) ->
    if not (Sys.file_exists (f:>string)) then
      Kernel.abort "file %a does not exist."
        Filepath.Normalized.pretty f;
    try
      Kernel.feedback "Parsing %a (external front-end)"
        Datatype.Filepath.pretty f;
      Hashtbl.find check_suffixes suf (f:>string)
    with Not_found ->
      Kernel.abort
        "could not find a suitable plugin for parsing %a."
        Filepath.Normalized.pretty f

let to_cil_cabs cpp_cmds_and_args f =
  try
    let cpp_command = List.assoc f cpp_cmds_and_args in
    let a,c = parse_cabs cpp_command f in
    Kernel.debug ~dkey:Kernel.dkey_file_print_one "result of parsing %s:@\n%a"
      (get_name f) Cil_printer.pp_file a;
    if Errorloc.had_errors () then raise Exit;
    a, c
  with exn when Errorloc.had_errors () ->
    if Kernel.Debug.get () >= 1 then raise exn
    else
      Kernel.abort "@[stopping on@ file %S@ that@ has@ errors.%t@]"
        (get_name f)
        (fun fmt ->
           if Filename.check_suffix (get_name f :> string) ".c" &&
              not (Kernel.is_debug_key_enabled Kernel.dkey_pp)
           then
             Format.fprintf fmt "@ Add@ '-kernel-msg-key pp'@ \
                                 for preprocessing command.")


let () =
  let handle f =
    let preprocess =
      replace_in_cpp_cmd (get_preprocessor_command ()) "-nostdinc"
    in
    let ppf =
      try Logic_preprocess.file ".c" preprocess f
      with Sys_error _ as e ->
        Kernel.abort "preprocessing of annotations failed (%s)"
          (Printexc.to_string e)
    in
    let path = Datatype.Filepath.of_string f in
    let (cil,(_,defs)) = Frontc.parse ppf () in
    cil.fileName <- path;
    safe_remove_file ppf;
    (cil,(path,defs))
  in
  new_file_type ".ci" handle



(* Keep defined entry point even if not defined, and possibly
   other unused globals according to relevant command-line parameters.
   This function is meant to be passed to {!Rmtmps.removeUnused}. *)
let isRoot g =
  let specs = Kernel.Keep_unused_specified_functions.get () in
  let keepTypes = Kernel.Keep_unused_types.get () in
  Rmtmps.isExportedRoot g ||
  match g with
  | GFun({svar = v; sspec = spec},_)
  | GFunDecl(spec,v,_) ->
    Kernel.MainFunction.get_plain_string () = v.vname
    (* Always keep the declaration of the entry point *)
    || (specs && not (is_empty_funspec spec))
  (* and the declarations carrying specifications according to the
     command line.*)
  | GType _ | GCompTag _ | GCompTagDecl _ | GEnumTag _ | GEnumTagDecl _ ->
    keepTypes
  | _ -> false

let files_to_cabs_cil files cpp_commands =
  Kernel.feedback ~level:2 "parsing";
  (* Parsing and merging must occur in the very same order.
     Otherwise the order of files on the command line will not be consistently
     handled. *)
  let cil_cabs = List.fold_left (fun acc f -> to_cil_cabs cpp_commands f :: acc) [] files in
  let cil_files, cabs_files = List.split cil_cabs in
  (* fold_left reverses the list order.
     This is an issue with pre-registered files. *)
  let cil_files = List.rev cil_files in
  let cabs_files = List.rev cabs_files in
  Ast.UntypedFiles.set cabs_files;
  (* Perform symbolic merge of all files *)
  Kernel.feedback ~level:2 "symbolic link";
  let merged_file = Mergecil.merge cil_files "whole_program" in
  Logic_utils.complete_types merged_file;
  if Kernel.UnspecifiedAccess.get () then
    Undefined_sequence.check_sequences merged_file;
  merged_file, cabs_files
(* "Implicit" annotations are those added by the kernel with ACSL name
   'Frama_C_implicit_init'. Currently, this concerns statements that are
   generated to initialize local variables. *)
module Implicit_annotations =
  State_builder.Hashtbl
    (Property.Hashtbl)(Datatype.List(Property))
    (struct
      let name = "File.Implicit_annotations"
      let dependencies = [Annotations.code_annot_state]
      let size = 32
    end)

let () = Ast.add_linked_state Implicit_annotations.self

let () =
  Property_status.register_property_remove_hook
    (fun p ->
       if Implicit_annotations.mem p then begin
         Kernel.debug ~dkey:Kernel.dkey_file_annot
           "Removing implicit property %a" Property.pretty p;
         Implicit_annotations.remove p
       end)

let emit_status p hyps =
  Kernel.debug ~dkey:Kernel.dkey_file_annot
    "Marking implicit property %a as true" Property.pretty p;
  Property_status.emit Emitter.kernel ~hyps p Property_status.True

let emit_all_statuses _ =
  Kernel.debug ~dkey:Kernel.dkey_file_annot "Marking properties";
  Implicit_annotations.iter emit_status

let () = Ast.apply_after_computed emit_all_statuses

let add_annotation kf st a =
  Annotations.add_code_annot ~keep_empty:false Emitter.end_user ~kf st a;
  (* Now check if the annotation is valid by construction
     (provided normalization is correct). *)
  match a.annot_content with
  | AStmtSpec
      ([],
       ({ spec_behavior = [ { b_name = "Frama_C_implicit_init" } as bhv]})) ->
    let props =
      Property.ip_post_cond_of_behavior kf (Kstmt st) ~active:[] bhv
    in
    List.iter (fun p -> Implicit_annotations.add p []) props
  | _ -> ()

let synchronize_source_annot has_new_stmt kf =
  match kf.fundec with
  | Definition (fd,_) ->
    let (visitor:cilVisitor) = object
      inherit nopCilVisitor as super
      val block_with_user_annots = ref None
      val user_annots_for_next_stmt = ref []
      method! vstmt st =
        super#pop_stmt st;
        let father = super#current_stmt in
        super#push_stmt st;
        let is_in_same_block () = match !block_with_user_annots,father with
          | None, None -> true
          | Some block, Some stmt_father when block == stmt_father -> true
          | _, _ -> false
        in
        let synchronize_user_annot a = add_annotation kf st a in
        let synchronize_previous_user_annots () =
          if !user_annots_for_next_stmt <> [] then begin
            if is_in_same_block () then begin
              let my_annots = !user_annots_for_next_stmt in
              let post_action st =
                let treat_annot (has_annot,st) (st_ann, annot) =
                  if Logic_utils.is_annot_next_stmt annot then begin
                    if has_annot || st.labels <> [] || st_ann.labels <> []
                    then begin
                      st_ann.skind <- (Block (Cil.mkBlockNonScoping [st]));
                      has_new_stmt := true;
                      Annotations.add_code_annot
                        ~keep_empty:false Emitter.end_user ~kf st_ann annot;
                      (true, st_ann)
                    end else begin
                      add_annotation kf st annot;
                      (true,st)
                    end
                  end else begin
                    add_annotation kf st annot;
                    (true, st)
                  end
                in
                let (_,st) =
                  List.fold_left treat_annot (false,st) my_annots
                in
                st
              in
              block_with_user_annots:=None;
              user_annots_for_next_stmt:=[];
              ChangeDoChildrenPost(st,post_action)
            end
            else begin
              Kernel.warning ~current:true ~once:true
                "Ignoring previous annotation relative \
                 to next statement effects" ;
              block_with_user_annots := None ;
              user_annots_for_next_stmt := [];
              DoChildren
            end
          end else begin
            block_with_user_annots := None ;
            user_annots_for_next_stmt := [];
            DoChildren;
          end
        in
        let add_user_annot_for_next_stmt st annot =
          if !user_annots_for_next_stmt = [] then begin
            block_with_user_annots := father;
            user_annots_for_next_stmt := [st,annot]
          end else if is_in_same_block () then
            user_annots_for_next_stmt :=
              (st, annot)::!user_annots_for_next_stmt
          else begin
            Kernel.warning ~current:true ~once:true
              "Ignoring previous annotation relative to next statement \
               effects";
            block_with_user_annots := father;
            user_annots_for_next_stmt := [st, annot] ;
          end;
          ChangeTo (Cil.mkStmtOneInstr (Skip Cil_datatype.Location.unknown))
        in
        assert (!block_with_user_annots = None
                || !user_annots_for_next_stmt <> []);
        match st.skind with
        | Instr (Code_annot (annot,_)) ->
          (* Code annotation isn't considered as a real stmt.
             So, previous annotations should be relative to the next stmt.
             Only this [annot] may be synchronised to that stmt *)
          if Logic_utils.is_annot_next_stmt annot then
            (* Annotation relative to the effect of next statement *)
            add_user_annot_for_next_stmt st annot
          else
            (* Annotation relative to the current control point *)
            (match !user_annots_for_next_stmt with
             | [] -> synchronize_user_annot annot; DoChildren
             | _ ->
               (* we have an annotation relative to the next
                  real C statement somewhere above, and we have
                  not reached it yet. Just stack the current annotation.*)
               add_user_annot_for_next_stmt st annot)
        | Loop (annot, _, _, _, _) ->
          (* Synchronize previous annotations on that statement *)
          let res = synchronize_previous_user_annots () in
          (* Synchronize loop annotations on that statement *)
          List.iter synchronize_user_annot
            (List.sort (fun x y -> x.annot_id - y.annot_id) annot);
          res
        | _ ->
          (* Synchronize previous annotations on that statement *)
          synchronize_previous_user_annots () ;
    end
    in
    ignore (visitCilFunction visitor fd)
  | Declaration _ -> ()

let register_global = function
  | GFun (fundec, loc) ->
    let onerets = ref [] in
    let callback return goto = onerets := (return,goto) :: !onerets in
    (* ensure there is only one return *)
    Oneret.oneret ~callback fundec;
    (* Build the Control Flow Graph for all
         functions *)
    if Kernel.SimplifyCfg.get () then begin
      Cfg.prepareCFG ~keepSwitch:(Kernel.KeepSwitch.get ()) fundec;
      Cfg.clearCFGinfo fundec;
      Cfg.cfgFun fundec;
      (* prepareCFG may add additional labels that are not used in the end. *)
      Rmtmps.remove_unused_labels fundec;
    end;
    Globals.Functions.add (Definition(fundec,loc));
    let kf = Globals.Functions.get fundec.svar in
    (* Finally set property-status on oneret clauses *)
    List.iter
      (fun ((sret,b,pret),gotos) ->
         let ipreturns =
           Property.ip_of_ensures kf (Kstmt sret) b (Returns,pret) in
         let ipgotos = List.map
             (fun (sgot,agot) -> Property.ip_of_code_annot_single kf sgot agot)
             gotos in
         Implicit_annotations.add ipreturns ipgotos
      ) !onerets ;
  | GFunDecl (spec, f,loc) ->
    (* global prototypes *)
    let args =
      try Some (Cil.getFormalsDecl f) with Not_found -> None
    in
    (* Use a copy of the spec, as the original one will be erased by
       AST cleanup. *)
    let spec = { spec with spec_variant = spec.spec_variant } in
    Globals.Functions.add (Declaration(spec,f,args,loc))
  | GVarDecl (vi,_) when not vi.vdefined ->
    (* global variables declaration with no definitions *)
    Globals.Vars.add_decl vi
  | GVar (varinfo,initinfo,_) ->
    (* global variables definitions *)
    Globals.Vars.add varinfo initinfo;
  | GAnnot (annot,_loc) ->
    Annotations.add_global Emitter.end_user annot
  | _ -> ()

let computeCFG ~clear_id file =
  Cfg.clearFileCFG ~clear_id file;
  Cfg.computeFileCFG file

(* Remove (inplace) annotations that are physically in the AST (and that have
   been moved inside kernel tables) by turning them into Skip, then
   remove empty statements and blocks. *)
let cleanup file =
  let visitor = object(self)
    inherit Visitor.frama_c_inplace

    val mutable keep_stmt = Stmt.Set.empty

    val mutable changed = false

    method private remove_lexical_annotations stmt =
      match stmt.skind with
      | Instr(Code_annot(_,loc)) ->
        stmt.skind <- Instr(Skip(loc))
      | Loop (_::_, b1,l1,s1,s2) ->
        stmt.skind <- Loop ([], b1, l1, s1, s2)
      | _ -> ()

    method! vstmt_aux st =
      self#remove_lexical_annotations st;
      let loc = Stmt.loc st in
      if Annotations.has_code_annot st || st.labels <> [] || st.sattr <> [] then
        keep_stmt <- Stmt.Set.add st keep_stmt;
      match st.skind with
      | Block b ->
        (* queue is flushed afterwards*)
        let b' = Cil.visitCilBlock (self:>cilVisitor) b in
        (match b'.bstmts, b'.blocals, b'.bstatics with
         | [], [], [] -> changed <- true; st.skind <- (Instr (Skip loc))
         | _ -> if b != b' then st.skind <- Block b');
        SkipChildren
      | _ -> DoChildren

    method! vblock b =
      let optim b =
        b.bstmts <-
          List.filter
            (fun x ->
               not (Cil.is_skip x.skind) || Stmt.Set.mem x keep_stmt ||
               ( changed <- true; false) (* don't try this at home, kids...*)
            )
            b.bstmts;
        (* Now that annotations are in the table, we do not need to
           retain the block anymore.
        *)
        b.battrs <- List.filter
            (function
              | Attr(l,[]) when l = Cabs2cil.frama_c_keep_block -> false
              | _ -> true)
            b.battrs;
        b
      in
      (* uncomment if you don't want to consider scope of locals (see below) *)
      (* b.blocals <- [];*)
      ChangeDoChildrenPost(b,optim)

    method! vglob_aux = function
      | GFun (f,_) ->
        f.sspec <- Cil.empty_funspec ();
        (* uncomment if you dont want to treat scope of locals (see above)*)
        (* f.sbody.blocals <- f.slocals; *)
        DoChildren
      | GFunDecl(s,_,_) ->
        Logic_utils.clear_funspec s;
        SkipChildren
      | GType _ | GCompTag _ | GCompTagDecl _ | GEnumTag _
      | GEnumTagDecl _ | GVar _ | GVarDecl _ | GAsm _ | GPragma _ | GText _
      | GAnnot _  ->
        SkipChildren

    method! vfile f =
      ChangeDoChildrenPost
        (f,fun f -> if changed then begin
             Cfg.clearFileCFG ~clear_id:false f;
             Cfg.computeFileCFG f; f end
            else f)

    method! vinst _ = Cil.SkipChildren
    method! vexpr _ = Cil.SkipChildren
    method! vlval _ = Cil.SkipChildren
    method! vtype _ = Cil.SkipChildren
    method! vspec _ = Cil.SkipChildren
    method! vcode_annot _ = Cil.SkipChildren
  end
  in visitFramacFileSameGlobals visitor file

let print_renaming: Cil.cilVisitor = object
  inherit Cil.nopCilVisitor
  method! vvdec v =
    if v.vname <> v.vorig_name then begin
      Kernel.result ~current:true
        "Variable %s has been renamed to %s" v.vorig_name v.vname
    end;
    DoChildren
end

module Transform_before_cleanup =
  Hook.Build_ordered
    (struct module Id = Datatype.String type t = Cil_types.file end)
module Transform_after_cleanup =
  Hook.Build_ordered
    (struct module Id = Datatype.String type t = Cil_types.file end)
module Transform_after_parameter_change =
  Hook.Build_ordered
    (struct module Id = Datatype.String type t = State.t end)
let transform_parameters = ref State.Set.empty

type code_transformation_category =
  { name: string;
    before_id: Transform_before_cleanup.id;
    after_id: Transform_after_cleanup.id;
    prm_id: Transform_after_parameter_change.id }

let register_code_transformation_category s =
  { name = s;
    before_id = Transform_before_cleanup.register_key s;
    after_id = Transform_after_cleanup.register_key s;
    prm_id = Transform_after_parameter_change.register_key s }

module Cfg_recomputation_queue =
  State_builder.Set_ref(Cil_datatype.Fundec.Set)
    (struct
      let name = "File.Cfg_recomputation_queue"
      let dependencies = [Ast.self]
    end)

let () = Ast.add_linked_state Cfg_recomputation_queue.self

let must_recompute_cfg f = Cfg_recomputation_queue.add f

let recompute_cfg _ =
  (* just in case f happens to modify the CFG *)
  Cfg_recomputation_queue.iter
    (fun f -> Cfg.clearCFGinfo ~clear_id:false f; Cfg.cfgFun f);
  Cfg_recomputation_queue.clear ()

let add_transform_parameter
    ~before ~after name f (p:(module Parameter_sig.S)) =
  let module P = (val p: Parameter_sig.S) in
  let hook self =
    (* hook is launched if AST already exists and the apply was triggered by
       the corresponding option change *)
    if State.equal self P.self && Ast.is_computed () then begin
      Kernel.feedback ~dkey:Kernel.dkey_file_transform
        "applying %s to current AST, after option %s changed"
        name.name P.option_name;
      f (Ast.get());
      recompute_cfg ();
      if Kernel.Check.get () then
        Filecheck.check_ast
          ("after code transformation: " ^ name.name ^
           " triggered by " ^ P.option_name)
    end
  in
  (* P.add_set_hook must be done only once. *)
  if not (State.Set.mem P.self !transform_parameters) then begin
    transform_parameters:=State.Set.add P.self !transform_parameters;
    P.add_set_hook (fun _ _ -> Transform_after_parameter_change.apply P.self)
  end;
  Transform_after_parameter_change.extend name.prm_id hook;
  List.iter
    (fun b ->
       Transform_after_parameter_change.add_dependency name.prm_id b.prm_id)
    before;
  List.iter
    (fun a ->
       Transform_after_parameter_change.add_dependency a.prm_id name.prm_id)
    after

let transform_and_check name is_normalized f ast =
  let printer =
    if is_normalized then Printer.pp_file else Cil_printer.pp_file
  in
  Kernel.feedback
    ~dkey:Kernel.dkey_file_transform
    "applying %s to file:@\n%a" name printer ast;
  f ast;
  recompute_cfg ();
  if Kernel.Check.get () then begin
    Filecheck.check_ast
      ~is_normalized  ~ast ("after code transformation: " ^ name);
  end

let add_code_transformation_before_cleanup
    ?(deps:(module Parameter_sig.S) list = [])
    ?(before=[]) ?(after=[]) name f =
  Transform_before_cleanup.extend
    name.before_id (transform_and_check name.name false f);
  List.iter
    (fun b ->
       Transform_before_cleanup.add_dependency name.before_id b.before_id)
    before;
  List.iter
    (fun a ->
       Transform_before_cleanup.add_dependency a.before_id name.before_id)
    after;
  List.iter (add_transform_parameter ~before ~after name f) deps

let add_code_transformation_after_cleanup
    ?(deps:(module Parameter_sig.S) list = [])  ?(before=[]) ?(after=[])
    name f =
  Transform_after_cleanup.extend name.after_id
    (transform_and_check name.name true f);
  List.iter
    (fun b ->
       Transform_after_cleanup.add_dependency name.after_id b.after_id) before;
  List.iter
    (fun a ->
       Transform_after_cleanup.add_dependency a.after_id name.after_id) after;
  List.iter (add_transform_parameter ~before ~after name f) deps

let syntactic_constant_folding ast =
  if Kernel.Constfold.get () then
    Cil.visitCilFileSameGlobals (Cil.constFoldVisitor true) ast

let constfold = register_code_transformation_category "constfold"

let () =
  let deps = [ (module Kernel.Constfold: Parameter_sig.S) ] in
  add_code_transformation_after_cleanup
    ~deps constfold syntactic_constant_folding

let () =
  let constglobfold = register_code_transformation_category "constglobfold" in
  let syntactic_const_globals_substitution ast =
    if Kernel.Constfold.get ()
    then
      Cil.visitCilFileSameGlobals
        Substitute_const_globals.constGlobSubstVisitor
        ast
  in
  add_code_transformation_before_cleanup
    ~deps:[ (module Kernel.Constfold: Parameter_sig.S) ]
    constglobfold
    syntactic_const_globals_substitution

let prepare_cil_file ast =
  Kernel.feedback ~level:2 "preparing the AST";
  computeCFG ~clear_id:true ast;
  if Kernel.Check.get () then begin
    Filecheck.check_ast ~is_normalized:false ~ast "initial AST"
  end;
  Kernel.feedback ~level:2 "First check done";
  if Kernel.Orig_name.get () then begin
    Cil.visitCilFileSameGlobals print_renaming ast
  end;
  Transform_before_cleanup.apply ast;
  (* Remove unused temp variables and globals. *)
  Kernel.feedback ~level:2 "cleaning unused parts";
  Rmtmps.removeUnused ~isRoot ast;
  if Kernel.Check.get () then begin
    Filecheck.check_ast ~is_normalized:false ~ast "Removed temp vars"
  end;
  (try
     List.iter register_global ast.globals
   with Globals.Vars.AlreadyExists(vi,_) ->
     Kernel.fatal
       "Trying to add the same varinfo twice: %a (vid:%d)"
       Printer.pp_varinfo vi vi.vid);
  Kernel.feedback ~level:2 "register globals done";
  (* NB: register_global also calls oneret, which might introduce new
     statements and new annotations tied to them. Since sid are set by cfg,
     we must compute it again before annotation synchronisation *)
  Cfg.clearFileCFG ~clear_id:false ast;
  Cfg.computeFileCFG ast;
  let recompute = ref false in
  Globals.Functions.iter (synchronize_source_annot recompute);
  (* We might also introduce new blocks for synchronization. *)
  if !recompute then begin
    Cfg.clearFileCFG ~clear_id:false ast;
    Cfg.computeFileCFG ast;
  end;
  cleanup ast;
  Ast.set_file ast;
  (* Check that normalization is correct. *)
  if Kernel.Check.get() then begin
    Filecheck.check_ast ~ast "AST after normalization";
  end;
  Globals.Functions.iter Annotations.register_funspec;
  if Kernel.Check.get () then begin
    Filecheck.check_ast ~ast "AST after annotation registration"
  end;
  Transform_after_cleanup.apply ast;
  (* reset tables depending on AST in case they have been computed during
     the transformation. *)
  Ast.set_file ast

let fill_built_ins () =
  if Cil.selfMachine_is_computed () then begin
    Kernel.debug "Machine is computed, just fill the built-ins";
    Cil_builtins.init_builtins ();
  end else begin
    Kernel.debug "Machine is not computed, initialize everything";
    Cil.initCIL ~initLogicBuiltins:(Logic_builtin.init()) (get_machdep ());
  end;
  (* Fill logic tables with builtins *)
  Logic_env.Builtins.apply ();
  Logic_env.prepare_tables ()

let init_project_from_cil_file prj file =
  let selection =
    State_selection.diff
      State_selection.full
      (State_selection.list_union
         (List.map State_selection.with_dependencies
            [Cil_builtins.Builtin_functions.self;
             Ast.self;
             Files.pre_register_state]))
  in
  Project.copy ~selection prj;
  Project.on prj (fun file -> fill_built_ins (); prepare_cil_file file) file

let files_pre_register_state = Files.pre_register_state

module Global_annotation_graph = struct
  module Base =
    Graph.Imperative.Digraph.Concrete(Cil_datatype.Global)
  include Base
  include Graph.Traverse.Dfs(Base)
  include Graph.Topological.Make(Base)
end

let find_typeinfo ty =
  let module F = struct exception Found of global end in
  let globs = (Ast.get()).globals in
  try
    List.iter
      (fun g -> match g with
         | GType (ty',_) when ty == ty' -> raise (F.Found g)
         | GType (ty',_) when ty.tname = ty'.tname ->
           Kernel.fatal
             "Lost sharing between definition and declaration of type %s"
             ty.tname
         | _ -> ())
      globs;
    Kernel.fatal "Reordering AST: unknown typedef for %s"  ty.tname
  with F.Found g -> g

let extract_logic_infos g =
  let rec aux acc = function
    | Dfun_or_pred (li,_) | Dinvariant (li,_) | Dtype_annot (li,_) -> li :: acc
    | Dvolatile _ | Dtype _ | Dlemma _
    | Dmodel_annot _ | Dextended _ -> acc
    | Daxiomatic(_,l,_,_) -> List.fold_left aux acc l
  in aux [] g

let find_logic_info_decl li =
  let module F = struct exception Found of global end in
  let globs = (Ast.get()).globals in
  try
    List.iter
      (fun g -> match g with
         | GAnnot (ga,_) ->
           if
             List.exists
               (fun li' -> Logic_info.equal li li')
               (extract_logic_infos ga)
           then raise (F.Found g)
         | _ -> ())
      globs;
    Kernel.fatal "Reordering AST: unknown declaration \
                  for logic function or predicate %s"
      li.l_var_info.lv_name
  with F.Found g -> g

class reorder_ast: Visitor.frama_c_visitor =
  let unique_name_recursive_axiomatic =
    let i = ref 0 in
    fun () ->
      if !i = 0 then begin incr i; "__FC_recursive_axiomatic" end
      else begin
        let res = "__FC_recursive_axiomatic_" ^ (string_of_int !i) in
        incr i; res
      end
  in
  object(self)
    inherit Visitor.frama_c_inplace
    val mutable known_enuminfo = Enuminfo.Set.empty
    val mutable known_compinfo = Compinfo.Set.empty
    val mutable known_typeinfo = Typeinfo.Set.empty
    val mutable known_var = Varinfo.Set.empty
    val mutable known_logic_info = Logic_info.Set.empty
    val mutable local_logic_info = Logic_info.Set.empty

    (* globals that have to be declared before current declaration. *)
    val mutable needed_decls = []
    (* global annotations are treated separately, as they need special
       care when revisiting their content *)
    val mutable needed_annots = []

    val current_annot = Stack.create ()

    val subvisit = Stack.create ()

    val typedefs = Stack.create ()

    val logic_info_deps = Global_annotation_graph.create ()

    method private add_known_enuminfo ei =
      known_enuminfo <- Enuminfo.Set.add ei known_enuminfo

    method private add_known_compinfo ci =
      known_compinfo <- Compinfo.Set.add ci known_compinfo

    method private add_known_type ty =
      known_typeinfo <- Typeinfo.Set.add ty known_typeinfo

    method private add_known_var vi =
      known_var <- Varinfo.Set.add vi known_var

    method private add_known_logic_info li =
      known_logic_info <- Logic_info.Set.add li known_logic_info

    method private add_needed_decl g =
      needed_decls <- g :: needed_decls

    method private add_needed_annot g =
      needed_annots <- g :: needed_annots

    method private add_annot_depend g =
      try
        let g' = Stack.top current_annot in
        if g == g' then ()
        else
          Global_annotation_graph.add_edge
            logic_info_deps g g' (* g' depends upon g *)
      with Stack.Empty ->
        Global_annotation_graph.add_vertex logic_info_deps g
    (* Otherwise, if we only have one annotation to take care of,
       the graph will be empty... *)

    method private add_known_annots g =
      let lis = extract_logic_infos g in
      List.iter self#add_known_logic_info lis

    method private clear_deps () =
      needed_decls <- [];
      needed_annots <- [];
      Stack.clear current_annot;
      Stack.clear typedefs;
      Global_annotation_graph.clear logic_info_deps

    method private make_annots g =
      let g =
        match g with
        | [ g ] -> g
        | _ -> (* We'll eventually add some globals, but the value returned
                  by visitor itself is supposed to be a singleton. Everything
                  is done in post-action.
               *)
          Kernel.fatal "unexpected result of visiting global when reordering"
      in
      let deps =
        if Global_annotation_graph.nb_vertex logic_info_deps = 0 then []
        else if Global_annotation_graph.has_cycle logic_info_deps then begin
          (* Assumption: elements from the stdlib are not part of a cycle with
             others logic functions, i.e. the stdlib is well-formed.  *)
          let entries =
            Global_annotation_graph.fold
              (fun g acc ->
                 let stdlib =
                   Cil.findAttribute "fc_stdlib" (Cil_datatype.Global.attr g)
                 in
                 let key =
                   match  stdlib with
                   | [ AStr s ] -> s
                   | _ -> ""
                 in
                 let elts =
                   try Datatype.String.Map.find key acc
                   with Not_found -> []
                 in
                 Datatype.String.Map.add key (g::elts) acc
              )
              logic_info_deps Datatype.String.Map.empty
          in
          Datatype.String.Map.fold
            (fun k l res ->
               let attr = if k = "" then [] else [ Attr("fc_stdlib", [AStr k])] in
               let entries =
                 List.fold_left
                   (fun acc g ->
                      match g with GAnnot (g,_) -> g :: acc | _ -> acc)
                   [] l
               in
               (GAnnot
                  (Daxiomatic
                     (unique_name_recursive_axiomatic (),
                      entries, attr,
                      Location.unknown),
                   Location.unknown))::res)
            entries []
        end else begin
          Global_annotation_graph.fold
            (fun ga acc -> ga :: acc) logic_info_deps []
        end
      in
      assert (List.length deps = List.length needed_annots);
      match g with
      | GAnnot _ -> List.rev deps
      (* g is already in the dependencies graph. *)
      | _ -> List.rev (g::deps)

    (* TODO: add methods for uses of undeclared identifiers.
       Use functions that maps an identifier to its decl.
       Don't forget to check for cycles for TNamed and logic_info.
    *)

    method! vtype ty =
      (match ty with
       | TVoid _ | TInt _ | TFloat _ | TPtr _
       | TFun _ | TBuiltin_va_list _ | TArray _ -> ()

       | TNamed (ty,_) ->
         let g = find_typeinfo ty in
         if not (Typeinfo.Set.mem ty known_typeinfo) then begin
           self#add_needed_decl g;
           Stack.push g typedefs;
           Stack.push true subvisit;
           ignore
             (Visitor.visitFramacGlobal (self:>Visitor.frama_c_visitor) g);
           ignore (Stack.pop typedefs);
           ignore (Stack.pop subvisit);
         end
         else
           Stack.iter
             (fun g' -> if g == g' then
                 Kernel.fatal
                   "Globals' reordering failed: \
                    recursive definition of type %s"
                   ty.tname)
             typedefs
       | TComp(ci,_) ->
         if not (Compinfo.Set.mem ci known_compinfo) then begin
           self#add_needed_decl (GCompTagDecl (ci,Location.unknown));
           self#add_known_compinfo ci
         end
       | TEnum(ei,_) ->
         if not (Enuminfo.Set.mem ei known_enuminfo) then begin
           self#add_needed_decl (GEnumTagDecl (ei, Location.unknown));
           self#add_known_enuminfo ei
         end);
      DoChildren

    method! vvrbl vi =
      if vi.vglob && not (Varinfo.Set.mem vi known_var) then begin
        if Cil.isFunctionType vi.vtype then
          self#add_needed_decl (GFunDecl (Cil.empty_funspec(),vi,vi.vdecl))
        else
          self#add_needed_decl (GVarDecl (vi,vi.vdecl));
        self#add_known_var vi;
      end;
      DoChildren

    method private logic_info_occurrence lv =
      if not (Logic_env.is_builtin_logic_function lv.l_var_info.lv_name) then
        begin
          let g = find_logic_info_decl lv in
          if not (Logic_info.Set.mem lv known_logic_info) then begin
            self#add_annot_depend g;
            Stack.push true subvisit;
            (* visit will also push g in needed_annot. *)
            ignore (Visitor.visitFramacGlobal (self:>Visitor.frama_c_visitor) g);
            ignore (Stack.pop subvisit)
          end else if List.memq g needed_annots then begin
            self#add_annot_depend g;
          end;
        end

    method private add_local_logic_info li =
      local_logic_info <- Logic_info.Set.add li local_logic_info

    method private remove_local_logic_info li =
      local_logic_info <- Logic_info.Set.remove li local_logic_info

    method private is_local_logic_info li =
      Logic_info.Set.mem li local_logic_info

    method! vlogic_var_use lv =
      let logic_infos = Annotations.logic_info_of_global lv.lv_name in
      (try
         self#logic_info_occurrence
           (List.find
              (fun x -> Cil_datatype.Logic_var.equal x.l_var_info lv)
              logic_infos)
       with Not_found -> ());
      DoChildren

    method! vterm t =
      match t.term_node with
      | Tlet(li,_) -> self#add_local_logic_info li;
        DoChildrenPost (fun t -> self#remove_local_logic_info li; t)
      | _ -> DoChildren

    method! vpredicate_node p =
      match p with
      | Plet(li,_) -> self#add_local_logic_info li;
        DoChildrenPost (fun t -> self#remove_local_logic_info li; t)
      | _ -> DoChildren

    method! vlogic_info_use lv =
      if not (self#is_local_logic_info lv) then self#logic_info_occurrence lv;
      DoChildren

    method! vglob_aux g =
      let is_subvisit = try Stack.top subvisit with Stack.Empty -> false in
      (match g with
       | GType (ty,_) -> self#add_known_type ty; self#add_needed_decl g
       | GCompTagDecl(ci,_) | GCompTag(ci,_) -> self#add_known_compinfo ci
       | GEnumTagDecl(ei,_) | GEnumTag(ei,_) -> self#add_known_enuminfo ei
       | GVarDecl(vi,_) | GVar (vi,_,_) | GFun({svar = vi},_) | GFunDecl (_,vi,_)
         -> self#add_known_var vi
       | GAsm _ | GPragma _ | GText _ -> ()
       | GAnnot (ga,_) ->
         Stack.push g current_annot;
         self#add_known_annots ga;
         Global_annotation_graph.add_vertex logic_info_deps g;
         self#add_needed_annot g);
      let post_action g =
        (match g with
         | [GAnnot _] -> ignore (Stack.pop current_annot)
         | _ -> ());
        if is_subvisit then g (* everything will be done at toplevel *)
        else begin
          let res = List.rev_append needed_decls (self#make_annots g) in
          self#clear_deps ();
          res
        end
      in
      DoChildrenPost post_action
  end

module Remove_spurious = struct
  type env =
    { typeinfos: Typeinfo.Set.t;
      compinfos: Compinfo.Set.t;
      enuminfos: Enuminfo.Set.t;
      varinfos: Varinfo.Set.t;
      logic_infos: Logic_info.Set.t;
      kept: global list;
    }

  let treat_one_global acc g =
    match g with
    | GType (ty,_) when Typeinfo.Set.mem ty acc.typeinfos -> acc
    | GType (ty,_) ->
      { acc with
        typeinfos = Typeinfo.Set.add ty acc.typeinfos;
        kept = g :: acc.kept }
    | GCompTag _ -> { acc with kept = g :: acc.kept }
    | GCompTagDecl(ci,_) when Compinfo.Set.mem ci acc.compinfos -> acc
    | GCompTagDecl(ci,_) ->
      { acc with
        compinfos = Compinfo.Set.add ci acc.compinfos;
        kept = g :: acc.kept }
    | GEnumTag _ -> { acc with kept = g :: acc.kept }
    | GEnumTagDecl(ei,_) when Enuminfo.Set.mem ei acc.enuminfos -> acc
    | GEnumTagDecl(ei,_) ->
      { acc with
        enuminfos = Enuminfo.Set.add ei acc.enuminfos;
        kept = g :: acc.kept }
    | GVarDecl(vi,_) | GFunDecl (_, vi, _)
      when Varinfo.Set.mem vi acc.varinfos -> acc
    | GVarDecl(vi,_) ->
      { acc with
        varinfos = Varinfo.Set.add vi acc.varinfos;
        kept = g :: acc.kept }
    | GVar _ | GFun _ | GFunDecl _ -> { acc with kept = g :: acc.kept }
    | GAsm _ | GPragma _ | GText _ -> { acc with kept = g :: acc.kept }
    | GAnnot (a,_) ->
      let lis = extract_logic_infos a in
      if List.exists (fun x -> Logic_info.Set.mem x acc.logic_infos) lis
      then acc
      else begin
        let known_li =
          List.fold_left (Extlib.swap Logic_info.Set.add) acc.logic_infos lis
        in
        { acc with
          kept = g::acc.kept;
          logic_infos = known_li;
        }
      end

  let empty =
    { typeinfos = Typeinfo.Set.empty;
      compinfos = Compinfo.Set.empty;
      enuminfos = Enuminfo.Set.empty;
      varinfos = Varinfo.Set.empty;
      logic_infos = Logic_info.Set.empty;
      kept = [];
    }

  let process file =
    let env = List.fold_left treat_one_global empty file.globals in
    file.globals <- List.rev env.kept

end

let reorder_custom_ast ast =
  Visitor.visitFramacFile (new reorder_ast) ast;
  Remove_spurious.process ast

let reorder_ast () = reorder_custom_ast (Ast.get())

(* Fill logic tables with builtins *)
let init_cil () =
  Cil.initCIL ~initLogicBuiltins:(Logic_builtin.init()) (get_machdep ());
  Logic_env.Builtins.apply ();
  Logic_env.prepare_tables ()

let re_included_file = Str.regexp "^[.]+ \\(.*\\)$"

let file_hash file =
  Digest.to_hex (Digest.file file)

let add_source_if_new tbl (fp : Filepath.Normalized.t) =
  if not (Hashtbl.mem tbl fp) then
    Hashtbl.replace tbl fp (file_hash (fp:>string))

(* Inserts, into the hashtbl of (Filepath.Normalized.t, Digest.t), [tbl],
   the included sources listed in [file],
   which contains the output of 'gcc -H -MM'. *)
let add_included_sources tbl file =
  let ic = open_in file in
  try
    while true; do
      let line = input_line ic in
      if Str.string_match re_included_file line 0 then
        let f = Str.matched_group 1 line in
        add_source_if_new tbl (Filepath.Normalized.of_string f)
    done;
    assert false
  with End_of_file ->
    close_in ic

let print_all_sources out all_sources_tbl =
  let elems =
    Hashtbl.fold (fun f hash acc ->
        (Filepath.Normalized.to_pretty_string f, hash) :: acc)
      all_sources_tbl []
  in
  let sorted_elems =
    List.sort (fun (f1, _) (f2, _) -> Extlib.compare_ignore_case f1 f2) elems
  in
  if Filepath.Normalized.is_special_stdout out then begin
    (* text format, to stdout *)
    Kernel.feedback "Audit: all used sources, with md5 hashes:@\n%a"
      (Pretty_utils.pp_list ~sep:"@\n"
         (Pretty_utils.pp_pair ~sep:": "
            Format.pp_print_string Format.pp_print_string)) sorted_elems
  end else begin
    (* json format, into file [out] *)
    let json =
      `Assoc
        [("sources",
          `Assoc (List.map (fun (f, hash) -> f, `String hash) sorted_elems)
         )]
    in
    try Json.merge_object out json
    with Json.CannotMerge _ ->
      Kernel.failure "%s: error when writing json file %a."
        Kernel.AuditPrepare.option_name Filepath.Normalized.pretty out
  end

let compute_sources_table cpp_commands =
  let all_sources_tbl = Hashtbl.create 7 in
  let process_file (file, cmd_opt) =
    add_source_if_new all_sources_tbl (get_filepath file);
    match cmd_opt with
    | None -> ()
    | Some (cpp_cmd, _ppf, _sl) ->
      let tmp_file = create_temp_file "audit_produce_sources" ".txt" in
      let tmp_file = (tmp_file :> string) in
      let cmd_for_sources = cpp_cmd ^ " -H -MM >/dev/null 2>" ^ tmp_file in
      let exit_code = Sys.command cmd_for_sources in
      if exit_code = 0
      then add_included_sources all_sources_tbl tmp_file
      else
        let cause_frama_c_compliant =
          if Kernel.CppGnuLike.get () then "" else
            Format.asprintf
              "\nPlease ensure preprocessor is Frama-C compliant \
               (see option %s)" Kernel.CppGnuLike.option_name
        in
        Kernel.abort "error running command to obtain included sources \
                      (exit code %d):@\n%s%s"
          exit_code cmd_for_sources cause_frama_c_compliant;
  in
  List.iter process_file cpp_commands;
  all_sources_tbl

let source_hashes_of_json path =
  try
    let json = Json.from_file path in
    let open Yojson.Basic.Util in
    json |> member "sources" |> to_assoc |>
    List.map (fun (k, h) -> k, to_string h)
  with
  | Yojson.Json_error msg ->
    Kernel.abort "error reading %a: %s"
      Filepath.Normalized.pretty path msg
  | Yojson.Basic.Util.Type_error (msg, v) ->
    Kernel.abort "error reading %a: %s - %s"
      Filepath.Normalized.pretty path msg
      (Yojson.Basic.pretty_to_string v)

let check_source_hashes expected actual_table =
  let checked, diffs =
    Hashtbl.fold (fun fp hash (acc_checked, acc_diffs) ->
        let fp = Filepath.Normalized.to_pretty_string fp in
        let expected_hash = List.assoc_opt fp expected in
        let checked = Datatype.String.Set.add fp acc_checked in
        let diffs =
          if Some hash = expected_hash then acc_diffs
          else (fp, hash, expected_hash) :: acc_diffs
        in
        checked, diffs
      ) actual_table (Datatype.String.Set.empty, [])
  in
  if diffs <> [] then begin
    let diffs =
      List.sort (fun (fp1, _, _) (fp2, _, _) ->
          Extlib.compare_ignore_case fp1 fp2) diffs
    in
    List.iter (fun (fp, got, expected) ->
        Kernel.warning ~wkey:Kernel.wkey_audit
          "different hashes for %s: got %s, expected %s"
          fp got (Option.value ~default:("<none> (not in list)") expected)
      ) diffs
  end;
  let expected_names = List.map fst expected in
  let missing =
    List.filter (fun fp -> not (Datatype.String.Set.mem fp checked))
      expected_names
  in
  if missing <> [] then begin
    let missing = List.sort Extlib.compare_ignore_case missing in
    Kernel.warning ~wkey:Kernel.wkey_audit
      "missing files:@\n%a"
      (Pretty_utils.pp_list ~sep:"@\n" Format.pp_print_string) missing
  end

let print_and_exit cpp_commands =
  let print_cpp_cmd (cpp_cmd, _ppf, _) =
    Kernel.result "Preprocessing command:@.%s" cpp_cmd
  in
  List.iter (fun (_f, ocmd) -> Option.iter print_cpp_cmd ocmd) cpp_commands;
  raise Cmdline.Exit

let prepare_audit () =
  let audit_path = Kernel.AuditPrepare.get () in
  if not (Filepath.Normalized.is_empty audit_path) then
    let files = Files.get () in (* Allow pre-registration of prologue files *)
    let cpp_commands = List.map (fun f -> (f, build_cpp_cmd f)) files in
    let all_sources_tbl = compute_sources_table cpp_commands in
    print_all_sources audit_path all_sources_tbl;
    (* This is normally done by another hook at normal exit, but it is done
       before our hook, so we need to redo it. *)
    if not (Filepath.Normalized.is_special_stdout audit_path) then
      Kernel.feedback "Audit: sources list written to: %a@."
        Filepath.Normalized.pretty audit_path

let () = Cmdline.at_normal_exit prepare_audit

let prepare_from_c_files () =
  init_cil ();
  let files = Files.get () in (* Allow pre-registration of prolog files *)
  let cpp_commands = List.map (fun f -> (f, build_cpp_cmd f)) files in
  if Kernel.PrintCppCommands.get () then print_and_exit cpp_commands;
  let audit_check_path = Kernel.AuditCheck.get () in
  if not (Filepath.Normalized.is_empty audit_check_path) then begin
    let all_sources_tbl = compute_sources_table cpp_commands in
    let expected_hashes = source_hashes_of_json audit_check_path in
    check_source_hashes expected_hashes all_sources_tbl
  end;
  let cil, cabs_files = files_to_cabs_cil files cpp_commands in
  prepare_cil_file cil;
  (* prepare_cil_file may call syntactic transformers, that will ultimately
     reset the untyped AST. Restore it here. *)
  Ast.UntypedFiles.set cabs_files

let init_project_from_visitor ?(reorder=false) prj
    (vis:Visitor.frama_c_visitor) =
  if not (Visitor_behavior.is_copy vis#behavior)
  || not (Project.equal prj (Option.get vis#project))
  then
    Kernel.fatal
      "Visitor does not copy or does not operate on correct project.";
  Project.on prj init_cil ();
  let old_ast = Ast.get () in
  let ast = visitFramacFileCopy vis old_ast in
  let finalize ast =
    computeCFG ~clear_id:false ast;
    Ast.set_file ast
  in
  let selection = State_selection.with_dependencies Ast.self in
  Project.on ~selection prj finalize ast;
  (* reorder _before_ check. *)
  if reorder then Project.on prj reorder_ast ();
  if Kernel.Check.get() then begin
    let name = prj.Project.name in
    Project.on prj (Filecheck.check_ast ~ast) ("AST of " ^ name);
    assert
      (Kernel.verify (old_ast == Ast.get())
         "Creation of project %s modifies original project"  name);
    Filecheck.check_ast ("Original AST after creation of " ^ name)
  end

let prepare_from_visitor ?reorder prj visitor =
  let visitor = visitor prj in
  init_project_from_visitor ?reorder prj visitor

let create_project_from_visitor ?reorder ?(last=true) prj_name visitor =
  let selection =
    State_selection.list_union
      (List.map State_selection.with_dependencies
         [ Kernel.Files.self; Files.pre_register_state ])
  in
  let selection = State_selection.diff State_selection.full selection in
  let prj = Project.create_by_copy ~selection ~last prj_name in
  (* reset projectified parameters to their default values *)
  let temp = Project.create "File.temp" in
  Project.copy
    ~selection:(Parameter_state.get_reset_selection ()) ~src:temp prj;
  Project.remove ~project:temp ();
  prepare_from_visitor ?reorder prj visitor;
  prj

let init_from_c_files files =
  (match files with [] -> () | _ :: _ -> Files.register files);
  prepare_from_c_files ()

let init_from_cmdline () =
  let prj1 = Project.current () in
  if Kernel.Copy.get () then begin
    let selection =
      State_selection.list_union
        (List.map State_selection.with_dependencies
           [ Cil_builtins.Builtin_functions.self;
             Logic_env.Logic_info.self;
             Logic_env.Logic_type_info.self;
             Logic_env.Logic_ctor_info.self;
             Ast.self ])
    in
    Project.clear ~selection ();
    let prj2 = Project.create_by_copy ~last:false "debug_copy_prj" in
    Project.set_current prj2;
  end;
  let files = Kernel.Files.get () in
  if files = [] && not !Fc_config.is_gui then Kernel.warning "no input file.";
  let files = List.map (fun f -> from_filename f) files in
  try
    init_from_c_files files;
    if Kernel.Check.get () then begin
      Filecheck.check_ast "Copy of original AST"
    end;
    if Kernel.Copy.get () then begin
      Project.on prj1 fill_built_ins ();
      prepare_from_visitor prj1 (fun prj -> new Visitor.frama_c_copy prj);
      Project.set_current prj1;
    end;
  with Ast.Bad_Initialization s ->
    Kernel.fatal "@[<v 0>Cannot initialize from C files@ \
                  Kernel raised Bad_Initialization %s@]" s

let init_from_cmdline =
  Journal.register
    "File.init_from_cmdline"
    (Datatype.func Datatype.unit Datatype.unit)
    init_from_cmdline

let init_from_c_files =
  Journal.register
    "File.init_from_c_files"
    (Datatype.func (Datatype.list ty) Datatype.unit)
    init_from_c_files

let prepare_from_c_files =
  Journal.register
    "File.prepare_from_c_files"
    (Datatype.func Datatype.unit Datatype.unit)
    prepare_from_c_files

let () = Ast.set_default_initialization
    (fun () ->
       if Files.is_computed () then prepare_from_c_files ()
       else init_from_cmdline ())

let pp_file_to fmt_opt =
  let pp_ast = Printer.pp_file in
  let ast = Ast.get () in
  (match fmt_opt with
   | None -> Kernel.CodeOutput.output (fun fmt -> pp_ast fmt ast)
   | Some fmt -> pp_ast fmt ast)

let unjournalized_pretty prj (fmt_opt:Format.formatter option) () =
  Project.on prj pp_file_to fmt_opt

let journalized_pretty_ast =
  Journal.register "File.pretty_ast"
    (Datatype.func3
       ~label1:("prj",Some Project.current) Project.ty
       ~label2:("fmt",Some (fun () -> None))
       (let module O = Datatype.Option(Datatype.Formatter) in
        O.ty)
       Datatype.unit Datatype.unit)
    unjournalized_pretty

let pretty_ast ?(prj=Project.current ()) ?fmt () =
  journalized_pretty_ast prj fmt ()

let create_rebuilt_project_from_visitor
    ?reorder ?last ?(preprocess=false) prj_name visitor =
  let prj = create_project_from_visitor ?reorder ?last prj_name visitor in
  try
    let f =
      let name = "frama_c_project_" ^ prj_name ^ "_" in
      let ext = if preprocess then ".c" else ".i" in
      let debug = Kernel.Debug.get () > 0 in
      create_temp_file ~debug name ext
    in
    let cout = open_out (f :> string) in
    let fmt = Format.formatter_of_out_channel cout in
    unjournalized_pretty prj (Some fmt) ();
    let redo () =
      (*      Kernel.feedback "redoing initialization on file %s" f;*)
      Files.reset ();
      init_from_c_files [ if preprocess then from_filename f else NoCPP f ]
    in
    Project.on prj redo ();
    prj
  with Sys_error s ->
    Kernel.abort "cannot create temporary file: %s" s

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
