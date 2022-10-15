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

(* ************************************************************************* *)
(** {2 Kernel as an almost standard plug-in} *)
(* ************************************************************************* *)

module FcPlugin = Plugin

let () = Plugin.register_kernel ()

module P = Plugin.Register
    (struct
      let name = ""
      let shortname = ""
      let help = "General options provided by the Frama-C kernel"
    end)

include (P: Plugin.S_no_log)
include Cmdline.Kernel_log

let dkey_alpha = register_category "alpha"

let dkey_alpha_undo = register_category "alpha:undo"

let dkey_asm_contracts = register_category "asm:contracts"

let dkey_ast = register_category "ast"

let dkey_builtins = register_category "builtins"

let dkey_check = register_category "check"

let dkey_constfold = register_category "constfold"

let dkey_comments = register_category "parser:comments"

let dkey_dataflow = register_category "dataflow"

let dkey_dataflow_scc = register_category "dataflow:scc"

let dkey_dominators = register_category "dominators"

let dkey_emitter = register_category "emitter"
let dkey_emitter_clear = register_category "emitter:clear"

let dkey_exn_flow = register_category "exn_flow"

let dkey_file_annot = register_category "file:annotation"

let dkey_file_print_one = register_category "file:print-one"

let dkey_file_transform = register_category "file:transformation"

let dkey_file_source = register_category "file:source"

let dkey_filter = register_category "filter"

let dkey_globals = register_category "globals"

let dkey_kf_blocks = register_category "kf:blocks"

let dkey_linker = register_category "linker"

let dkey_linker_find = register_category "linker:find"

let dkey_loops = register_category "natural-loops"

let dkey_parser = register_category "parser"
let dkey_rmtmps = register_category "parser:rmtmps"
let dkey_referenced = register_category "parser:referenced"

let dkey_pp = register_category "pp"
let dkey_pp_logic = register_category "pp:logic"
let dkey_compilation_db = register_category "pp:compilation-db"

let dkey_print_bitfields = register_category "printer:bitfields"

let dkey_print_builtins = register_category "printer:builtins"

let dkey_print_logic_coercions = register_category "printer:logic-coercions"

let dkey_print_logic_types = register_category "printer:logic-types"

let dkey_print_attrs = register_category "printer:attrs"

let dkey_print_sid = register_category "printer:sid"

let dkey_print_unspecified = register_category "printer:unspecified"

let dkey_print_vid = register_category "printer:vid"

let dkey_print_field_offsets = register_category "printer:field-offsets"

let dkey_prop_status = register_category "prop-status"

let dkey_prop_status_emit = register_category "prop-status:emit"

let dkey_prop_status_merge = register_category "prop-status:merge"

let dkey_prop_status_reg = register_category "prop-status:register"

let dkey_prop_status_graph = register_category "prop-status:graph"

let dkey_task = register_category "task"

let dkey_typing_global = register_category "typing:global"

let dkey_typing_init = register_category "typing:initializer"

let dkey_typing_chunk = register_category "typing:chunk"

let dkey_typing_cast = register_category "typing:cast"

let dkey_typing_pragma = register_category "typing:pragma"

let dkey_ulevel = register_category "ulevel"

let dkey_visitor = register_category "visitor"

let wkey_annot_error = register_warn_category "annot-error"
let () = set_warn_status wkey_annot_error Log.Wabort

let wkey_ghost_already_ghost = register_warn_category "ghost:already-ghost"
let () = set_warn_status wkey_ghost_already_ghost Log.Wfeedback

let wkey_ghost_bad_use = register_warn_category "ghost:bad-use"
let () = set_warn_status wkey_ghost_bad_use Log.Werror

let wkey_acsl_float_compare = register_warn_category "acsl-float-compare"
let () = set_warn_status wkey_acsl_float_compare Log.Winactive

let wkey_conditional_feature =
  register_warn_category "parser:conditional-feature"

let wkey_drop_unused = register_warn_category "linker:drop-conflicting-unused"

let wkey_implicit_conv_void_ptr =
  register_warn_category "typing:implicit-conv-void-ptr"

let wkey_incompatible_types_call =
  register_warn_category "typing:incompatible-types-call"

let wkey_incompatible_pointer_types =
  register_warn_category "typing:incompatible-pointer-types"

let wkey_inconsistent_specifier =
  register_warn_category "typing:inconsistent-specifier"

let wkey_int_conversion =
  register_warn_category "typing:int-conversion"

let wkey_cert_exp_46 = register_warn_category "CERT:EXP:46"

let wkey_cert_msc_37 = register_warn_category "CERT:MSC:37"

let wkey_cert_msc_38 = register_warn_category "CERT:MSC:38"
let () = set_warn_status wkey_cert_msc_38 Log.Werror

let wkey_cert_exp_10 = register_warn_category "CERT:EXP:10"
let () = set_warn_status wkey_cert_exp_10 Log.Winactive

let wkey_check_volatile = register_warn_category "check:volatile"

let wkey_jcdb = register_warn_category "pp:compilation-db"
let () = set_warn_status wkey_jcdb Log.Wonce

let wkey_implicit_function_declaration = register_warn_category
    "typing:implicit-function-declaration"

let wkey_no_proto = register_warn_category "typing:no-proto"

let wkey_missing_spec = register_warn_category "annot:missing-spec"

let wkey_multi_from = register_warn_category "annot:multi-from"

let wkey_decimal_float = register_warn_category "parser:decimal-float"
let () = set_warn_status wkey_decimal_float Log.Wonce

let wkey_acsl_extension = register_warn_category "acsl-extension"

let wkey_cmdline = register_warn_category "cmdline"

let wkey_audit = register_warn_category "audit"
let () = set_warn_status wkey_audit Log.Werror

let wkey_parser_unsupported = register_warn_category "parser:unsupported"

let wkey_asm = register_warn_category "asm:clobber"

let wkey_unnamed_typedef = register_warn_category "parser:unnamed-typedef"

let wkey_file_not_found = register_warn_category "file:not-found"
let () = set_warn_status wkey_file_not_found Log.Wfeedback

(* ************************************************************************* *)
(** {2 Specialised functors for building kernel parameters} *)
(* ************************************************************************* *)

module type Input = sig
  include Parameter_sig.Input
  val module_name: string
end

module type Input_with_arg = sig
  include Parameter_sig.Input_with_arg
  val module_name: string
end

module Bool(X:sig include Input val default: bool end) =
  P.Bool
    (struct
      let () = Parameter_customize.set_module_name X.module_name
      include X
    end)

module False(X: Input) =
  P.False
    (struct
      let () = Parameter_customize.set_module_name X.module_name
      include X
    end)

module True(X: Input) =
  P.True
    (struct
      let () = Parameter_customize.set_module_name X.module_name
      include X
    end)

module Int (X: sig val default: int include Input_with_arg end) =
  P.Int
    (struct
      let () = Parameter_customize.set_module_name X.module_name
      include X
    end)

module Zero(X:Input_with_arg) =
  P.Zero
    (struct
      let () = Parameter_customize.set_module_name X.module_name
      include X
    end)

module String
    (X: sig include Input_with_arg val default: string end) =
  P.String
    (struct
      let () = Parameter_customize.set_module_name X.module_name
      include X
    end)

module String_list(X: Input_with_arg) =
  P.String_list
    (struct
      let () = Parameter_customize.set_module_name X.module_name
      include X
    end)

module Filepath_list
    (X: sig
       include Input_with_arg
       val existence: Filepath.existence
       val file_kind: string
     end) =
  P.Filepath_list
    (struct
      let () = Parameter_customize.set_module_name X.module_name
      include X
    end)

module Filepath_map
    (X: sig
       include Input_with_arg
       val existence: Filepath.existence
       val file_kind: string
     end) =
  P.Filepath_map
    (struct
      include Datatype.String
      type key = Filepath.Normalized.t
      let of_string ~key:_ ~prev:_ s = s
      let to_string ~key:_ s = s
    end)
    (struct
      let () = Parameter_customize.set_module_name X.module_name
      include X
      let default = Datatype.Filepath.Map.empty
    end)

module Kernel_function_set(X: Input_with_arg) =
  P.Kernel_function_set
    (struct
      let () = Parameter_customize.set_module_name X.module_name
      include X
    end)

(* ************************************************************************* *)
(** {2 Installation Information} *)
(* ************************************************************************* *)

let () = Parameter_customize.set_group help
let () = Parameter_customize.set_cmdline_stage Cmdline.Exiting
let () = Parameter_customize.do_not_journalize ()
let () = Parameter_customize.set_negative_option_name ""
module GeneralHelp =
  False
    (struct
      let option_name = "--help"
      let help = "display a general help"
      let module_name = "GeneralHelp"
    end)
let run_help () = if GeneralHelp.get () then Cmdline.help () else Cmdline.nop
let () = Cmdline.run_after_exiting_stage run_help
let () = GeneralHelp.add_aliases [ "-h"; "-help"]

let () = Parameter_customize.set_group help
let () = Parameter_customize.set_cmdline_stage Cmdline.Exiting
let () = Parameter_customize.do_not_journalize ()
let () = Parameter_customize.set_negative_option_name ""
module ListPlugins =
  False
    (struct
      let option_name = "--list-plugins"
      let help = "display a general help"
      let module_name = "ListPlugins"
    end)
let run_list_plugins () =
  if ListPlugins.get () then Cmdline.list_plugins () else Cmdline.nop
let () = Cmdline.run_after_exiting_stage run_list_plugins
let () = ListPlugins.add_aliases ["-plugins"; "--plugins"]

let () = Parameter_customize.set_group help
let () = Parameter_customize.set_cmdline_stage Cmdline.Early
let () = Parameter_customize.set_negative_option_name ""
module PrintConfig =
  False
    (struct
      let option_name = "-print-config"
      let module_name = "PrintConfig"
      let help = "print full config information"
    end)

let () = Parameter_customize.set_group help
let () = Parameter_customize.set_cmdline_stage Cmdline.Early
let () = Parameter_customize.set_negative_option_name ""
module PrintVersion =
  False(struct
    let option_name = "-print-version"
    let module_name = "PrintVersion"
    let help = "print the Frama-C version"
  end)
let () = PrintVersion.add_aliases [ "-v"; "-version" ; "--version" ]

let () = Parameter_customize.set_group help
let () = Parameter_customize.set_cmdline_stage Cmdline.Early
let () = Parameter_customize.set_negative_option_name ""
module PrintShare =
  False(struct
    let option_name = "-print-share-path"
    let module_name = "PrintShare"
    let help = "print the Frama-C share path"
  end)
let () = PrintShare.add_aliases [ "-print-path" ]

let () = Parameter_customize.set_group help
let () = Parameter_customize.set_cmdline_stage Cmdline.Early
let () = Parameter_customize.set_negative_option_name ""
module PrintLib =
  False(struct
    let option_name = "-print-lib-path"
    let module_name = "PrintLib"
    let help = "print the path of the Frama-C kernel library"
  end)
let () = PrintLib.add_aliases [ "-print-libpath" ]

let () = Parameter_customize.set_group help
let () = Parameter_customize.set_cmdline_stage Cmdline.Early
let () = Parameter_customize.set_negative_option_name ""
module PrintPluginPath =
  False
    (struct
      let option_name = "-print-plugin-path"
      let module_name = "PrintPluginPath"
      let help =
        "print the path where the Frama-C dynamic plug-ins are searched into"
    end)

let () = Parameter_customize.set_group help
let () = Parameter_customize.set_cmdline_stage Cmdline.Exiting
let () = Parameter_customize.set_negative_option_name ""
module PrintMachdep =
  False
    (struct
      let module_name = "PrintMachdep"
      let option_name = "-print-machdep"
      let help = "pretty print selected machdep"
    end)

let () = Parameter_customize.set_group help
let () = Parameter_customize.set_negative_option_name ""
module DumpDependencies =
  P.Empty_string
    (struct
      let option_name = "-dump-dependencies"
      let help = ""
      let arg_name = ""
    end)
let () =
  Extlib.safe_at_exit
    (fun () ->
       if not (DumpDependencies.is_default ()) then
         State_dependency_graph.dump (DumpDependencies.get ()))

let () = Parameter_customize.set_group help
let () = Parameter_customize.set_cmdline_stage Cmdline.Exiting
module PrintConfigJson =
  False
    (struct
      let module_name = "PrintConfigJson"
      let option_name = "-print-config-json"
      let help = "prints extensive data about Frama-C's configuration, in \
                  JSON format, and exits (experimental: the output format \
                  is very likely to change in future versions)."
    end)

let () = Parameter_customize.set_group help
let () = Parameter_customize.set_cmdline_stage Cmdline.Exiting
let () = Parameter_customize.do_not_journalize ()
let () = Parameter_customize.set_negative_option_name ""
module AutocompleteHelp =
  P.String_set
    (struct
      let option_name = "-autocomplete"
      let arg_name = "p1,p2,..."
      let help = "displays all Frama-C options, used for shell autocompletion. \
                  Prints options for the specified plugin names (or '@all' for \
                  all plugins). Note: for the kernel, use an empty string."
    end)

let _ =
  AutocompleteHelp.Category.enable_all
    []
    (object
      method fold: 'a. (string -> 'a -> 'a) -> 'a -> 'a =
        fun f acc ->
        FcPlugin.fold_on_plugins (fun p acc -> f p.FcPlugin.p_shortname acc) acc
      method mem name =
        try
          FcPlugin.iter_on_plugins
            (fun p -> if name = p.FcPlugin.p_shortname then raise Exit);
          false
        with Exit -> true
    end)

let () = Parameter_customize.set_group help
let () = Parameter_customize.set_cmdline_stage Cmdline.Extending
let () = Parameter_customize.do_not_journalize ()
let () = Parameter_customize.set_negative_option_name ""
module Explain =
  False
    (struct
      let option_name = "-explain"
      let help = "prints the help message for each option given in the \
                  command line"
      let module_name = "Explain"
    end)

let () =
  Cmdline.run_after_exiting_stage (fun () ->
      if Explain.get () then Cmdline.explain_cmdline ()
      else Cmdline.nop)
(* This option is processed in a special manner in [Cmdline].
   Nothing to be done here. *)

(* ************************************************************************* *)
(** {2 Output Messages} *)
(* ************************************************************************* *)

let () = Parameter_customize.set_group messages
let () = Parameter_customize.do_not_projectify ()
let () = Parameter_customize.do_not_journalize ()
let () = Parameter_customize.set_cmdline_stage Cmdline.Early
let () = Parameter_customize.is_reconfigurable ()
module GeneralVerbose =
  Int
    (struct
      let default = 1
      let option_name = "-verbose"
      let arg_name = "n"
      let help = "general level of verbosity"
      let module_name = "GeneralVerbose"
    end)
let () =
  (* line order below matters *)
  GeneralVerbose.set_range ~min:0 ~max:max_int;
  GeneralVerbose.add_set_hook (fun _ n -> Cmdline.Verbose_level.set n);
  match !Cmdline.Verbose_level.value_if_set with
  | None -> ()
  | Some n -> GeneralVerbose.set n

let () = Parameter_customize.set_group messages
let () = Parameter_customize.do_not_projectify ()
let () = Parameter_customize.do_not_journalize ()
let () = Parameter_customize.set_cmdline_stage Cmdline.Early
let () = Parameter_customize.is_reconfigurable ()
module GeneralDebug =
  Zero
    (struct
      let option_name = "-debug"
      let arg_name = "n"
      let help = "general level of debug"
      let module_name = "GeneralDebug"
    end)
let () =
  (* line order below matters *)
  GeneralDebug.set_range ~min:0 ~max:max_int;
  GeneralDebug.add_set_hook
    (fun old n ->
       if n = 0 then decr Plugin.positive_debug_ref
       else if old = 0 then incr Plugin.positive_debug_ref;
       Cmdline.Debug_level.set n);
  match !Cmdline.Debug_level.value_if_set with
  | None -> ()
  | Some n -> GeneralDebug.set n

let () = Parameter_customize.set_group messages
let () = Parameter_customize.set_negative_option_name ""
let () = Parameter_customize.set_cmdline_stage Cmdline.Early
let () = Parameter_customize.is_reconfigurable ()
let () = Parameter_customize.do_not_projectify ()
let () = Parameter_customize.do_not_journalize ()
module Quiet =
  Bool
    (struct
      let default = Cmdline.quiet
      let option_name = "-quiet"
      let module_name = "Quiet"
      let help = "sets -verbose and -debug to 0"
    end)
let () =
  Quiet.add_set_hook
    (fun _ b -> assert b; GeneralVerbose.set 0; GeneralDebug.set 0)

let () = Parameter_customize.set_group messages
let () = Parameter_customize.set_cmdline_stage Cmdline.Extended
let () = Parameter_customize.do_not_journalize ()
let () = Parameter_customize.do_not_projectify ()
module Unicode = struct
  include True
      (struct
        let option_name = "-unicode"
        let module_name = "Unicode"
        let help = "use utf8 in messages"
      end)
  (* This function behaves nicely with the Gui, that detects if command-line
     arguments have been set by the user at some point. One possible improvement
     would be to bypass journalization entirely, but this requires an API
     change in Plugin *)
  let without_unicode f arg =
    let old, default = get (), not (is_set ()) in
    off ();
    let r = f arg in
    if default then clear () else set old;
    r
end

let () = Parameter_customize.set_group messages
let () = Parameter_customize.do_not_projectify ()
let () = Parameter_customize.set_cmdline_stage Cmdline.Extending
module TTY =
  True
    (struct
      let option_name = "-tty"
      let module_name = "TTY"
      let help = "use terminal capabilities for feedback (when available)"
    end)
let () = Log.tty := TTY.get

let () = Parameter_customize.set_group messages
let () = Parameter_customize.do_not_projectify ()
module Time =
  P.Empty_string
    (struct
      let option_name = "-time"
      let arg_name = "filename"
      let help = "append process time and timestamp to <filename> at exit"
    end)

let () = Parameter_customize.set_group messages
let () = Parameter_customize.do_not_projectify ()
module SymbolicPath =
  Filepath_map
    (struct
      let option_name = "-add-symbolic-path"
      let module_name = "SymbolicPath"
      let arg_name = "path_1:name_1,...,path_n:name_n"
      let existence = Filepath.Indifferent
      let file_kind = "directory"
      let help =
        "When displaying file locations, replace (absolute) path with the \
         corresponding symbolic name"
    end)

let () =
  SymbolicPath.add_update_hook
    (fun _old map ->
       (* keep module [Filepath] synchronized with [SymbolicPath] *)
       Filepath.reset_symbolic_dirs ();
       Datatype.Filepath.Map.iter
         (fun n p -> Filepath.add_symbolic_dir p n) map)

(* [SymbolicPath] is better to be not projectified,
   but must be saved: use a fake state for saving it without projectifying it *)
module SymbolicPathFakeState =
  State_builder.Register
    (Datatype.Unit)
    (struct
      type t = unit
      let create () = ()
      let clear () = ()
      let get () = ()
      let set () = ()
      let clear_some_projects _f () = false
    end)
    (struct
      let name = "SymbolicPathFakeState"
      let unique_name = name
      let dependencies = []
    end)

let () =
  SymbolicPathFakeState.howto_marshal
    (fun () -> SymbolicPath.get ())
    (fun paths -> SymbolicPath.set paths)

(* ************************************************************************* *)
(** {2 Input / Output Source Code} *)
(* ************************************************************************* *)

let inout_source = add_group "Input/Output Source Code"

let () = Parameter_customize.set_group inout_source
module PrintCode =
  False
    (struct
      let module_name = "PrintCode"
      let option_name = "-print"
      let help = "pretty print original code with its comments"
    end)

let () = Parameter_customize.set_group inout_source
let () = Parameter_customize.do_not_projectify ()
module PrintAsIs =
  False
    (struct
      let module_name = "PrintAsIs"
      let option_name = "-print-as-is"
      let help = "when pretty-printing C code, try to print it as close as \
                  possible to the internal (Cil) representation"
    end)

let () = Parameter_customize.set_group inout_source
let () = Parameter_customize.do_not_projectify ()
module PrintComments =
  False
    (struct
      let module_name = "PrintComments"
      let option_name = "-keep-comments"
      let help = "try to keep comments in C code"
    end)

let () = Parameter_customize.set_group inout_source
let () = Parameter_customize.do_not_projectify ()
module PrintLibc =
  Bool
    (struct
      let module_name = "PrintLibc"
      let option_name = "-print-libc"
      let help = "when pretty-printing C code, keep prototypes coming \
                  from Frama-C standard library"
      let default = !Fc_config.is_gui (* always print by default on the GUI *)
    end)

let () = Parameter_customize.set_group inout_source
module PrintReturn =
  False
    (struct
      let module_name = "PrintReturn"
      let option_name = "-print-return"
      let help = "inline gotos to return statement"
    end)

module CodeOutput = struct

  let () = Parameter_customize.set_group inout_source
  include P.Filepath
      (struct
        let option_name = "-ocode"
        let arg_name = "filename"
        let existence = Filepath.Indifferent
        let file_kind = "source"
        let help =
          "when printing code, redirects the output to file <filename>"
      end)

  let streams = Hashtbl.create 7

  let output job =
    let file = get () in
    if Filepath.Normalized.(is_special_stdout file || is_empty file)
    then Log.print_delayed job
    else
      try
        let fmt =
          try fst (Hashtbl.find streams file)
          with Not_found ->
            let out = open_out (file:>string) in
            let fmt = Format.formatter_of_out_channel out in
            Hashtbl.add streams file (fmt,out) ; fmt
        in
        job fmt
      with Sys_error s ->
        warning
          "Fail to open file \"%a\" for code output@\nSystem error: %s.@\n\
           Code is output on stdout instead."
          Filepath.Normalized.pretty file s ;
        Log.print_delayed job

  let close_all () =
    Hashtbl.iter
      (fun file (fmt,cout) ->
         try
           Format.pp_print_flush fmt () ;
           close_out cout ;
         with Sys_error s ->
           failure
             "Fail to close output file \"%a\"@\nSystem error: %s."
             Filepath.Normalized.pretty file s)
      streams

  let () = Extlib.safe_at_exit close_all

end

let () = Parameter_customize.set_group inout_source
let () = Parameter_customize.do_not_projectify ()
module FloatNormal =
  False
    (struct
      let option_name = "-float-normal"
      let module_name = "FloatNormal"
      let help = "display floats with internal routine"
    end)

let () = Parameter_customize.set_group inout_source
let () = Parameter_customize.do_not_projectify ()
module FloatRelative =
  False
    (struct
      let option_name = "-float-relative"
      let module_name = "FloatRelative"
      let help = "display float intervals as [lower_bound ++ width]"
    end)

let () = Parameter_customize.set_group inout_source
let () = Parameter_customize.do_not_projectify ()
module FloatHex =
  False
    (struct
      let option_name = "-float-hex"
      let module_name = "FloatHex"
      let help = "display floats as hexadecimal"
    end)

let () = Parameter_customize.set_group inout_source
let () = Parameter_customize.do_not_projectify ()
module BigIntsHex =
  Int(struct
    let module_name = "BigIntsHex"
    let option_name = "-big-ints-hex"
    let arg_name = "max"
    let help = "display integers larger than <max> using hexadecimal \
                notation"
    let default = -1
  end)

let () = Parameter_customize.set_group inout_source
module EagerLoadSources =
  False(struct
    let module_name = "EagerLoadSources"
    let option_name = "-eager-load-sources"
    let help = "when loading a source, try to load all referenced sources \
                in memory"
  end)

let () = Parameter_customize.set_group inout_source
let () = Parameter_customize.do_not_projectify ()
module AstDiff =
  False
    (struct
      let option_name = "-ast-diff"
      let module_name = "AstDiff"
      let help = "creates a new project and computes a diff of the AST \
                  from the current one"
    end)

(* ************************************************************************* *)
(** {2 Save/Load} *)
(* ************************************************************************* *)

let saveload = add_group "Saving or Loading Data"

let () = Parameter_customize.set_group saveload
let () = Parameter_customize.do_not_projectify ()
module SaveState =
  P.Filepath
    (struct
      let option_name = "-save"
      let arg_name = "filename"
      let existence = Filepath.Indifferent
      let file_kind = "Frama-C state"
      let help = "at exit, save the session into file <filename>"
    end)

let () = Parameter_customize.set_group saveload
let () = Parameter_customize.set_cmdline_stage Cmdline.Loading
(* must be projectified: when loading, this option will be automatically
   reset *)
(*let () = Parameter_customize.do_not_projectify ()*)
module LoadState =
  P.Filepath
    (struct
      let option_name = "-load"
      let arg_name = "filename"
      let existence = Filepath.Must_exist
      let file_kind = "Frama-C state"
      let help = "load a previously-saved session from file <filename>"
    end)

let () = Parameter_customize.set_group saveload
let () = Parameter_customize.set_cmdline_stage Cmdline.Extending
let () = Parameter_customize.do_not_projectify ()
module AddPath =
  String_list
    (struct
      let option_name = "-add-path"
      let module_name = "AddPath"
      let arg_name = "DIR,..."
      let help = "Prepend directories to FRAMAC_PLUGIN for loading dynamic plug-ins"
    end)

let () = Parameter_customize.set_group saveload
let () = Parameter_customize.set_cmdline_stage Cmdline.Extending
let () = Parameter_customize.do_not_projectify ()
module LoadModule =
  String_list
    (struct
      let option_name = "-load-module"
      let module_name = "LoadModule"
      let arg_name = "SPEC,..."
      let help = "Dynamically load plug-ins, modules and scripts. \
                  Each <SPEC> can be an OCaml source or object file, with \
                  or without extension, or a Findlib package. \
                  Loading order is preserved and \
                  additional dependencies can be listed in *.depend files."
    end)
let () = LoadModule.add_aliases [ "-load-script" ]

let () = Parameter_customize.set_group saveload
let () = Parameter_customize.set_cmdline_stage Cmdline.Extending
let () = Parameter_customize.do_not_projectify ()
module AutoLoadPlugins =
  True
    (struct
      let option_name = "-autoload-plugins"
      let module_name = "AutoLoadPlugins"
      let help = "Automatically load all plugins in FRAMAC_PLUGIN."
    end)

let bootstrap_loader () =
  begin
    Dynamic.set_module_load_path (AddPath.get ());
    if AutoLoadPlugins.get () then Dynamic.load_plugin_path () ;
    List.iter Dynamic.load_module (LoadModule.get()) ;
  end

let () = Cmdline.load_all_plugins := bootstrap_loader

module Journal = struct
  let () = Parameter_customize.set_negative_option_name "-journal-disable"
  let () = Parameter_customize.set_cmdline_stage Cmdline.Early
  let () = Parameter_customize.set_group saveload
  let () = Parameter_customize.do_not_projectify ()
  module Enable = struct
    include Bool
        (struct
          let module_name = "Journal.Enable"
          let default = Cmdline.journal_enable
          let option_name = "-journal-enable"
          let help = "dump a journal while Frama-C exit"
        end)
    let is_set () = Cmdline.journal_isset
  end
  let () = Parameter_customize.set_group saveload
  let () = Parameter_customize.do_not_projectify ()
  module Name =
    String
      (struct
        let module_name = "Journal.Name"
        let option_name = "-journal-name"
        let default =
          let dir =
            (* duplicate code from Plugin.Session *)
            if Session.is_set ()
            then
              (Session.get () :> string)
            else
              try Sys.getenv "FRAMAC_SESSION"
              with Not_found -> "./.frama-c"
          in
          dir ^ "/frama_c_journal.ml"
        let arg_name = "s"
        let help = "set the filename of the journal"
      end)
  let () = Name.add_set_hook (fun _ s -> Journal.set_name s);
end

let () = Parameter_customize.set_cmdline_stage Cmdline.Extending
let () = Parameter_customize.set_group saveload
let () = Parameter_customize.do_not_projectify ()
module Session_dir =
  P.Filepath
    (struct
      let option_name = "-session"
      let arg_name = "path"
      let existence = Filepath.Indifferent
      let file_kind = "directory"
      let help = "directory in which session files are searched"
    end)
let () = Plugin.session_is_set_ref := Session_dir.is_set
let () = Plugin.session_ref := Session_dir.get

let () = Parameter_customize.set_cmdline_stage Cmdline.Extending
let () = Parameter_customize.set_group saveload
let () = Parameter_customize.do_not_projectify ()
module Config_dir =
  P.Filepath
    (struct
      let option_name = "-config"
      let arg_name = "path"
      let existence = Filepath.Indifferent
      let file_kind = "directory"
      let help = "directory in which configuration files are searched"
    end)
let () = Plugin.config_is_set_ref := Config_dir.is_set
let () = Plugin.config_ref := Config_dir.get

(* ************************************************************************* *)
(** {2 Parsing} *)
(* ************************************************************************* *)

let parsing = add_group "Parsing"

let () = Parameter_customize.set_group parsing
let () = Parameter_customize.do_not_reset_on_copy ()
let () = Parameter_customize.set_cmdline_stage Cmdline.Extended
module Machdep =
  String
    (struct
      let module_name = "Machdep"
      let option_name = "-machdep"
      let default =
        try Sys.getenv "FRAMAC_MACHDEP"
        with Not_found -> "x86_64"
      let arg_name = "machine"
      let help =
        "use <machine> as the current machine dependent configuration. \
         See \"-machdep help\" for a list. The environment variable \
         FRAMAC_MACHDEP can be used to override the default value. The command \
         line parameter still has priority over the default value"
    end)

let () = Parameter_customize.set_group parsing
let () = Parameter_customize.do_not_reset_on_copy ()
module ReadAnnot =
  True(struct
    let module_name = "ReadAnnot"
    let option_name = "-annot"
    let help = "read and parse annotations"
  end)

let () = Parameter_customize.set_group parsing
let () = Parameter_customize.do_not_reset_on_copy ()
module PreprocessAnnot =
  False(struct
    let module_name = "PreprocessAnnot"
    let option_name = "-pp-annot"
    let help =
      "pre-process annotations (if they are read). Set by default if \
       the pre-processor is GNU-like (see option -cpp-frama-c-compliant)"
  end)

let () = Parameter_customize.set_group parsing
let () = Parameter_customize.do_not_reset_on_copy ()
module CppCommand =
  P.Empty_string
    (struct
      let option_name = "-cpp-command"
      let arg_name = "cmd"
      let help = "<cmd> is used to build the preprocessing command.\n\
                  Default to $CPP environment variable or else \"gcc -C -E -I.\".\n\
                  If unset, the command is built as follows:\n\
                  CPP -o <preprocessed file> <source file>\n\
                  %1 and %2 can be used into CPP string to mark the position of <source file> \
                  and <preprocessed file> respectively"
    end)

let () = Parameter_customize.set_group parsing
let () = Parameter_customize.do_not_reset_on_copy ()
let () = Parameter_customize.no_category ()
module CppExtraArgs =
  String_list
    (struct
      let module_name = "CppExtraArgs"
      let option_name = "-cpp-extra-args"
      let arg_name = "args"
      let help = "additional arguments passed to the preprocessor while \
                  preprocessing the C code but not while preprocessing annotations"
    end)

let () = Parameter_customize.set_group parsing
let () = Parameter_customize.do_not_reset_on_copy ()
module CppExtraArgsPerFile =
  Filepath_map
    (struct
      let module_name = "CppExtraArgsPerFile"
      let option_name = "-cpp-extra-args-per-file"
      let arg_name = "file:flags"
      let existence = Filepath.Must_exist
      let file_kind = "source"
      let help =
        "when set, adds preprocessing arguments for each specified file. \
         To add arguments for all files, use -cpp-extra-args."
    end)

let () = Parameter_customize.set_group parsing
let () = Parameter_customize.do_not_reset_on_copy ()
module CppGnuLike =
  True
    (struct
      let module_name = "CppGnuLike"
      let option_name = "-cpp-frama-c-compliant"
      let help =
        "indicates that a custom pre-processor (see option -cpp-command) \
         accepts the same set of options as GNU cpp. Set it to false if you \
         have pre-processing issues with a custom pre-processor."
    end)

let () = Parameter_customize.set_group parsing
let () = Parameter_customize.do_not_reset_on_copy ()
module PrintCppCommands =
  False
    (struct
      let module_name = "PrintCppCommands"
      let option_name = "-print-cpp-commands"
      let help = "prints the preprocessing command(s) used by Frama-C \
                  and exits."
    end)

let () = Parameter_customize.set_group parsing
let () = Parameter_customize.do_not_reset_on_copy ()
module AuditPrepare =
  P.Filepath
    (struct
      let option_name = "-audit-prepare"
      let arg_name = "path"
      let existence = Filepath.Indifferent
      let file_kind = "json"
      let help = "produces audit-related information, such as the list of all \
                  source files used during parsing (including those in include \
                  directives) with checksums. Some plug-ins may produce \
                  additional audit-related information. \
                  Prints the information as JSON to the specified file, or \
                  if the file is '-', prints as text to the standard output. \
                  Requires -cpp-frama-c-compliant."
    end)

let () = Parameter_customize.set_group parsing
let () = Parameter_customize.do_not_reset_on_copy ()
module AuditCheck =
  P.Filepath
    (struct
      let option_name = "-audit-check"
      let arg_name = "path"
      let existence = Filepath.Must_exist
      let file_kind = "json"
      let help = "reads an audit JSON file (produced by -audit-prepare) and \
                  checks compliance w.r.t. it; e.g., if the source files \
                  were declared and have the expected checksum. \
                  Raises a warning (with warning key 'audit') in case of \
                  failed checks. \
                  Requires -cpp-frama-c-compliant."
    end)

let () = Parameter_customize.set_group parsing
let () = Parameter_customize.do_not_reset_on_copy ()
module FramaCStdLib =
  True
    (struct
      let module_name = "FramaCStdLib"
      let option_name = "-frama-c-stdlib"
      let help =
        "adds -I$FRAMAC_SHARE/libc to the options given to the cpp command. \
         If -cpp-frama-c-compliant is not false, also adds -nostdinc to prevent \
         inconsistent mix of system and Frama-C header files"
    end)

let () = Parameter_customize.set_group parsing
let () = Parameter_customize.do_not_reset_on_copy ()
module ContinueOnAnnotError =
  False(struct
    let module_name = "ContinueOnAnnotError"
    let option_name = "-continue-annot-error"
    let help =
      "[DEPRECATED: Use -kernel-warn-key annot-error instead] \
       When an annotation fails to type-check, emit a warning \
       and discard the annotation instead of generating an error \
       (errors in C are still fatal)"
  end)
let () =
  ContinueOnAnnotError.add_set_hook
    (fun _ f ->
       warning ~once:true
         "-continue-annot-error is deprecated. \
          Use -kernel-warn-key annot-error (or similar option) instead";
       set_warn_status wkey_annot_error (if f then Log.Wactive else Log.Wabort))

let () = Parameter_customize.set_group parsing
module Orig_name =
  False(struct
    let option_name = "-orig-name"
    let module_name = "Orig_name"
    let help = "prints a message each time a variable is renamed"
  end)

let () = Parameter_customize.set_group parsing
let () = Parameter_customize.do_not_reset_on_copy ()
module ImplicitFunctionDeclaration =
  String(struct
    let option_name = "-implicit-function-declaration"
    let arg_name = "action"
    let help =
      "[DEPRECATED: Use \
       -kernel-warn-key typing:implicit-function-declaration=error instead] \
       Warn or abort when a function is called before it has been declared \
       (non-C99 compliant); action must be ignore, warn, or error"
    let default = "warn"
    let module_name = "ImplicitFunctionDeclaration"
  end)
let () = ImplicitFunctionDeclaration.set_possible_values ["ignore"; "warn"; "error"]
let () =
  ImplicitFunctionDeclaration.add_set_hook
    (fun _ s ->
       warning ~once:true
         "-implicit-function-declaration is deprecated, \
          use '-kernel-warn-key typing:implicit-function-declaration' \
          (or similar options) instead.";
       let status =
         if s = "ignore" then Log.Winactive else
         if s = "warn" then Log.Wactive else
         if s = "error" then Log.Wabort
         else fatal "invalid value: %s" s
       in
       set_warn_status wkey_implicit_function_declaration status)


let () = Parameter_customize.set_group parsing
let () = Parameter_customize.do_not_reset_on_copy ()
module WarnDecimalFloat =
  String(struct
    let option_name = "-warn-decimal-float"
    let arg_name = "freq"
    let help = "[DEPRECATED: Use -kernel-warn-key \
                parser:decimal-float=active (or inactive) instead] \
                Warn when floating-point constants cannot be exactly \
                represented; freq must be one of none, once or all"
    let default = "once"
    let module_name = "WarnDecimalFloat"
  end)
let () = WarnDecimalFloat.set_possible_values ["none"; "once"; "all"]
let () = WarnDecimalFloat.add_set_hook
    (fun _ s ->
       let status =
         if s = "none" then Log.Winactive
         else if s = "once" then Log.Wonce
         else if s = "all" then Log.Wactive
         else fatal "invalid value: %s" s
       in
       set_warn_status wkey_decimal_float status)

let () = Parameter_customize.set_group parsing
let () = Parameter_customize.do_not_reset_on_copy ()
module C11 =
  False(struct
    let option_name = "-c11"
    let help = "allow C11 constructs (experimental; partial support only)"
    let module_name = "C11"
  end)

let () = Parameter_customize.set_group parsing
let () = Parameter_customize.do_not_reset_on_copy ()
module JsonCompilationDatabase =
  P.Filepath
    (struct
      let option_name = "-json-compilation-database"
      let arg_name = "path"
      let file_kind = "directory or json"
      let existence = Filepath.Must_exist
      let help =
        "when set, preprocessing of each file will include corresponding \
         flags (e.g. -I, -D) from the JSON compilation database \
         specified by <path>. If <path> is a directory, use \
         '<path>/compile_commands.json'. Disabled by default."
    end)

(* ************************************************************************* *)
(** {2 Customizing Normalization} *)
(* ************************************************************************* *)

let normalisation = add_group "Customizing Normalization"

let () = Parameter_customize.set_group normalisation
module UnrollingLevel =
  Zero
    (struct
      let module_name = "UnrollingLevel"
      let option_name = "-ulevel"
      let arg_name = "l"
      let help =
        "unroll loops n times (defaults to 0) before analyzes. \
         A negative value hides UNROLL loop pragmas."
    end)

let () = Parameter_customize.set_group normalisation
module UnrollingForce =
  Bool
    (struct
      let module_name = "UnrollingForce"
      let default = false
      let option_name = "-ulevel-force"
      let help =
        "ignore UNROLL loop pragmas disabling unrolling."
    end)

let () = Parameter_customize.set_group normalisation
let () = Parameter_customize.do_not_reset_on_copy ()
let () = Parameter_customize.is_invisible ()
module LogicalOperators =
  Bool
    (struct
      let module_name = "LogicalOperators"
      let option_name = "-keep-logical-operators"
      let default = false
      let help =
        " UNSUPPORTED :  use it only if you really know what you are doing. \
         Use logical operators (&& and ||) instead of conversion into \
         conditional statements when possible."
    end)

let () = Parameter_customize.set_group normalisation
let () = Parameter_customize.do_not_reset_on_copy ()
module Enums =
  P.String
    (struct
      let option_name = "-enums"
      let arg_name = "repr"
      let default = "gcc-enums"
      let help =
        "use <repr> to decide how enumerated types should be represented. \
         -enums help gives the list of available representations (default: "
        ^ default ^ ")"
    end)
let enum_reprs = ["gcc-enums"; "gcc-short-enums"; "int";]
let () = Enums.set_possible_values ("help"::enum_reprs)
let () =
  Enums.add_set_hook
    (fun _ o -> if o = "help" then
        feedback "Possible enums representation are: %a"
          (Pretty_utils.pp_list ~sep:", " Format.pp_print_string)
          enum_reprs)

let () = Parameter_customize.set_group normalisation
module SimplifyCfg =
  False
    (struct
      let module_name = "SimplifyCfg"
      let option_name = "-simplify-cfg"
      let help =
        "remove break, continue and switch statements before analyses"
    end)

let () = Parameter_customize.set_group normalisation
module KeepSwitch =
  False(struct
    let option_name = "-keep-switch"
    let module_name = "KeepSwitch"
    let help = "keep switch statements despite -simplify-cfg"
  end)

let () = Parameter_customize.set_group normalisation
let () = Parameter_customize.set_negative_option_name "-remove-unused-specified-functions"
module Keep_unused_specified_functions =
  True(struct
    let option_name = "-keep-unused-specified-functions"
    let module_name = "Keep_unused_specified_functions"
    let help = "keep specified-but-unused functions"
  end)

let () = Parameter_customize.set_group normalisation
let () = Parameter_customize.set_negative_option_name "-remove-unused-types"
module Keep_unused_types =
  False(struct
    let option_name = "-keep-unused-types"
    let module_name = "Keep_unused_types"
    let help = "keep unused types (false by default)"
  end)

let () = Parameter_customize.set_group normalisation
module SimplifyTrivialLoops =
  True(struct
    let option_name = "-simplify-trivial-loops"
    let module_name = "SimplifyTrivialLoops"
    let help = "simplify trivial loops, such as do ... while(0) loops"
  end)

let () = Parameter_customize.set_group normalisation
module Constfold =
  False
    (struct
      let option_name = "-constfold"
      let module_name = "Constfold"
      let help = "fold all constant expressions in the code before analysis"
    end)

let () = Parameter_customize.set_group normalisation
let () = Parameter_customize.do_not_reset_on_copy ()
module InitializedPaddingLocals =
  True
    (struct
      let option_name = "-initialized-padding-locals"
      let module_name = "InitializedPaddingLocals"
      let help = "Implicit initialization of locals sets padding bits to 0. \
                  If false, padding bits are left uninitialized. \
                  Defaults to true."
    end)

let () = Parameter_customize.set_group normalisation
module AggressiveMerging =
  False
    (struct
      let option_name = "-aggressive-merging"
      let module_name = "AggressiveMerging"
      let help = "merge function definitions modulo renaming \
                  (defaults to false)"
    end)

let () = Parameter_customize.set_group normalisation
module AsmContractsGenerate =
  True
    (struct
      let option_name = "-asm-contracts"
      let module_name = "AsmContractsGenerate"
      let help = "generate contracts for assembly code written according \
                  to gcc's extended syntax"
    end)

let () = Parameter_customize.set_group normalisation
module AsmContractsAutoValidate =
  False
    (struct
      let option_name = "-asm-contracts-auto-validate"
      let module_name = "AsmContractsAutoValidate"
      let help = "automatically mark contracts generated from asm as valid \
                  (defaults to false)"
    end)

let () = Parameter_customize.set_group normalisation
module RemoveExn =
  False
    (struct
      let option_name = "-remove-exn"
      let module_name = "RemoveExn"
      let help =
        "transforms throw and try/catch statements to normal C functions. \
         Disabled by default, unless input source language has \
         has an exception mechanism."
    end)

module Files = struct

  let () = Parameter_customize.is_invisible ()
  let () = Parameter_customize.no_category ()
  include Filepath_list
      (struct
        let option_name = ""
        let module_name = "Files"
        let arg_name = ""
        let help = ""
        let file_kind = "source"
        let existence = Filepath.Must_exist
      end)
  let () = Cmdline.use_cmdline_files set

end

let () = Parameter_customize.set_group normalisation
module AllowDuplication =
  True(struct
    let option_name = "-allow-duplication"
    let module_name = "AllowDuplication"
    let help =
      "allow duplication of small blocks during normalization"
  end)

let () = Parameter_customize.set_group normalisation
module DoCollapseCallCast =
  True(struct
    let option_name = "-collapse-call-cast"
    let module_name = "DoCollapseCallCast"
    let help =
      "Allow some implicit casts between returned value of a function \
       and the lvalue it is assigned to."
  end)

let normalization_parameters () =
  let norm = Cmdline.Group.name normalisation in
  let kernel = Plugin.get_from_name "" in
  Hashtbl.find kernel.Plugin.p_parameters norm


(* ************************************************************************* *)
(** {2 Analysis Options} *)
(* ************************************************************************* *)

let analysis_options = add_group "Analysis Options"

let () = Parameter_customize.set_group analysis_options
module MainFunction =
  String
    (struct
      let module_name = "MainFunction"
      let default = "main"
      let option_name = "-main"
      let arg_name = "f"
      let help = "use <f> as entry point for analysis. See \"-lib-entry\" \
                  if this is not for a complete application. Defaults to main"
    end)

let () = Parameter_customize.set_group analysis_options
module LibEntry =
  False
    (struct
      let module_name = "LibEntry"
      let option_name = "-lib-entry"
      let help ="run analysis for an incomplete application e.g. an API call. See the -main option to set the entry point"
    end)

let () = Parameter_customize.set_group analysis_options
module UnspecifiedAccess =
  False(struct
    let module_name = "UnspecifiedAccess"
    let option_name = "-unspecified-access"
    let help = "do not assume that read/write accesses occurring \
                between sequence points are separated"
  end)

let () = Parameter_customize.set_negative_option_name "-unsafe-arrays"
let () = Parameter_customize.set_group analysis_options
module SafeArrays =
  True
    (struct
      let module_name = "SafeArrays"
      let option_name = "-safe-arrays"
      let help = "for multidimensional arrays or arrays that are fields \
                  inside structs, assume that accesses are in bounds"
    end)

let () = Parameter_customize.set_group analysis_options
let () = Parameter_customize.do_not_reset_on_copy ()
module AbsoluteValidRange = struct
  module Info = struct
    let option_name = "-absolute-valid-range"
    let arg_name = "min-max"
    let help = "min and max must be integers in decimal, hexadecimal (0x, 0X), octal (0o) or binary (0b) notation and fit in 64 bits. Assume that that all absolute addresses outside of the [min-max] range are invalid. In the absence of this option, all absolute addresses are assumed to be invalid"
    let default = ""
    let module_name = "AbsoluteValidRange"
  end
  include String(Info)
end

(* Signed overflows are undefined behaviors. *)
let () = Parameter_customize.set_group analysis_options
let () = Parameter_customize.do_not_reset_on_copy ()
module SignedOverflow =
  True
    (struct
      let module_name = "SignedOverflow"
      let option_name = "-warn-signed-overflow"
      let help = "generate alarms for signed operations that overflow."
    end)

(* Unsigned overflows are ok, but might not always be a behavior the programmer
   wants. *)
let () = Parameter_customize.set_group analysis_options
let () = Parameter_customize.do_not_reset_on_copy ()
module UnsignedOverflow =
  False
    (struct
      let module_name = "UnsignedOverflow"
      let option_name = "-warn-unsigned-overflow"
      let help = "generate alarms for unsigned operations that overflow"
    end)

(* Left shifts on negative integers are undefined behaviors. *)
let () = Parameter_customize.set_group analysis_options
let () = Parameter_customize.do_not_reset_on_copy ()
module LeftShiftNegative =
  True
    (struct
      let module_name = "LeftShiftNegative"
      let option_name = "-warn-left-shift-negative"
      let help = "generate alarms for signed left shifts on negative values."
    end)

(* Right shift on negative integers are implementation-defined behaviors. *)
let () = Parameter_customize.set_group analysis_options
let () = Parameter_customize.do_not_reset_on_copy ()
module RightShiftNegative =
  False
    (struct
      let module_name = "RightShiftNegative"
      let option_name = "-warn-right-shift-negative"
      let help = "generate alarms for signed right shifts on negative values."
    end)

(* Signed downcast are implementation-defined behaviors. *)
let () = Parameter_customize.set_group analysis_options
let () = Parameter_customize.do_not_reset_on_copy ()
module SignedDowncast =
  False
    (struct
      let module_name = "SignedDowncast"
      let option_name = "-warn-signed-downcast"
      let help = "generate alarms when signed downcasts may exceed the \
                  destination range"
    end)

(* Unsigned downcasts are ok, but might not always be a behavior the programmer
   wants. *)
let () = Parameter_customize.set_group analysis_options
let () = Parameter_customize.do_not_reset_on_copy ()
module UnsignedDowncast =
  False
    (struct
      let module_name = "UnsignedDowncast"
      let option_name = "-warn-unsigned-downcast"
      let help = "generate alarms when unsigned downcasts may exceed the \
                  destination range"
    end)

(* Pointer downcasts are undefined behaviors. *)
let () = Parameter_customize.set_group analysis_options
let () = Parameter_customize.do_not_reset_on_copy ()
module PointerDowncast =
  True
    (struct
      let module_name = "PointerDowncast"
      let option_name = "-warn-pointer-downcast"
      let help = "generate alarms when a pointer is converted into an integer \
                  but may not be in the range of the destination type."
    end)

(* Not finite floats are ok, but might not always be a behavior the programmer
   wants. *)
let () = Parameter_customize.set_group analysis_options
let () = Parameter_customize.do_not_reset_on_copy ()
module SpecialFloat =
  String
    (struct
      let module_name = "SpecialFloat"
      let option_name = "-warn-special-float"
      let default = "non-finite"
      let arg_name = "none|nan|non-finite"
      let help = "generate alarms when special floats are produced: never, \
                  only on NaN, or on infinite floats and NaN (by default)."
    end)
let () = SpecialFloat.set_possible_values ["none"; "nan"; "non-finite"]

let () = Parameter_customize.set_group analysis_options
let () = Parameter_customize.do_not_reset_on_copy ()
module InvalidBool =
  True
    (struct
      let module_name = "InvalidBool"
      let option_name = "-warn-invalid-bool"
      let help = "generate alarms when trap representations are read from \
                  _Bool lvalues."
    end)

let () = Parameter_customize.set_group analysis_options
let () = Parameter_customize.do_not_reset_on_copy ()
module InvalidPointer =
  False
    (struct
      let module_name = "InvalidPointer"
      let option_name = "-warn-invalid-pointer"
      let help = "generate alarms when invalid pointers are created."
    end)

(* ************************************************************************* *)
(** {2 Sequencing options} *)
(* ************************************************************************* *)

let seq = add_group "Sequencing Options"

let () =
  Cmdline.add_option_without_action
    "-then"
    ~plugin:""
    ~group:seq
    ~help:"parse options before `-then' and execute Frama-C \
           accordingly, then parse options after `-then' and re-execute Frama-C"
    ~visible:true
    ~ext_help:""
    ()

let () =
  Cmdline.add_option_without_action
    "-then-last"
    ~plugin:""
    ~group:seq
    ~help:"like `-then', but the second group of actions is executed \
           on the last project created by a program transformer."
    ~visible:true
    ~ext_help:""
    ()

let () =
  Cmdline.add_option_without_action
    "-then-replace"
    ~plugin:""
    ~group:seq
    ~help:"like `-then-last', but also remove the previous current project."
    ~visible:true
    ~ext_help:""
    ()

let () =
  Cmdline.add_option_without_action
    "-then-on"
    ~plugin:""
    ~argname:"p"
    ~group:seq
    ~help:"like `-then', but the second group of actions is executed \
           on project <p>"
    ~visible:true
    ~ext_help:""
    ()

(* ************************************************************************* *)
(** {2 Project-related options} *)
(* ************************************************************************* *)

let project = add_group "Project-related Options"

let () = Parameter_customize.set_group project
let () = Parameter_customize.do_not_projectify ()
module Set_project_as_default =
  False(struct
    let module_name = "Set_project_as_default"
    let option_name = "-set-project-as-default"
    let help = "the current project becomes the default one \
                (and so future '-then' sequences are applied on it)"
  end)

let () = Parameter_customize.set_group project
let () = Parameter_customize.do_not_projectify ()
module Remove_projects =
  P.Make_set
    (struct
      include Project.Datatype
      let of_singleton_string = P.no_element_of_string
      let of_string s =
        try Project.from_unique_name s
        with Project.Unknown_project ->
          raise (P.Cannot_build ("no project '" ^ s ^ "'"))
      let to_string = Project.get_unique_name
    end)
    (struct
      let option_name = "-remove-projects"
      let arg_name = "p1, ..., pn"
      let help = "remove the given projects <p1>, ..., <pn>. \
                  @all_but_current removes all projects but the current one."
      let default = Project.Datatype.Set.empty
      let dependencies = []
    end)

let _ =
  Remove_projects.Category.enable_all
    []
    (object
      method fold: 'a. (Project.t -> 'a -> 'a) -> 'a -> 'a =
        fun f acc -> Project.fold_on_projects (fun acc p -> f p acc) acc
      method mem _p = true (* impossible to build an unregistered project *)
    end)

let _ =
  Remove_projects.Category.add
    "all_but_current"
    []
    (object
      method fold: 'a. (Project.t -> 'a -> 'a) -> 'a -> 'a =
        fun f acc ->
        Project.fold_on_projects
          (fun acc p -> if Project.is_current p then acc else f p acc)
          acc
      method mem p = not (Project.is_current p)
    end)

let () =
  Cmdline.run_after_configuring_stage
    (fun () ->
       (* clear "-remove-projects" before itering over (a copy of) its contents
          in order to prevent warnings about dangling pointer deletion (since it
          is itself projectified and so contains a pointer to the project being
          removed). *)
       let s = Remove_projects.get () in
       Remove_projects.clear ();
       Project.Datatype.Set.iter (fun project -> Project.remove ~project ()) s)

(* ************************************************************************* *)
(** {2 Checks} *)
(* ************************************************************************* *)

let checks = add_group "Checks"

let () = Parameter_customize.set_group checks
let () = Parameter_customize.do_not_projectify ()
let () = Parameter_customize.do_not_reset_on_copy ()
module Check =
  False(struct
    let option_name = "-check"
    let module_name = "Check"
    let help = "performs consistency checks over the Abstract Syntax \
                Tree"
  end)

let () = Parameter_customize.set_group checks
let () = Parameter_customize.do_not_projectify ()
module Copy =
  False(struct
    let option_name = "-copy"
    let module_name = "Copy"
    let help =
      "always perform a copy of the original AST before analysis begin"
  end)

let () = Parameter_customize.set_group checks
let () = Parameter_customize.do_not_projectify ()
let () = Parameter_customize.set_negative_option_name ""
module TypeCheck =
  True(struct
    let module_name = "TypeCheck"
    let option_name = "-typecheck"
    let help = "forces typechecking of the source files"
  end)

(* ************************************************************************* *)
(** {2 Other options} *)
(* ************************************************************************* *)

[@@@warning "-60"]
(* Warning: these options are parsed and used directly from Cmdline *)

let () = Parameter_customize.set_negative_option_name ""
let () = Parameter_customize.set_cmdline_stage Cmdline.Early
let () = Parameter_customize.is_invisible ()
module NoType =
  Bool
    (struct
      let module_name = "NoType"
      let default = not Cmdline.use_type
      let option_name = "-no-type"
      let help = ""
    end)

let () = Parameter_customize.set_negative_option_name ""
let () = Parameter_customize.set_cmdline_stage Cmdline.Early
let () = Parameter_customize.is_invisible ()
module NoObj =
  Bool
    (struct
      let module_name = "NoObj"
      let default = not Cmdline.use_obj
      let option_name = "-no-obj"
      let help = ""
    end)

let () = Parameter_customize.set_group project
let () = Parameter_customize.set_negative_option_name ""
let () = Parameter_customize.set_cmdline_stage Cmdline.Early
module Deterministic =
  Bool
    (struct
      let module_name = "Deterministic"
      let default = not Cmdline.deterministic
      let option_name = "-deterministic"
      let help = ""
    end)

let () = Parameter_customize.set_group checks
let () = Parameter_customize.do_not_projectify ()
let () = Parameter_customize.set_negative_option_name ""
let () = Parameter_customize.set_cmdline_stage Cmdline.Early
module Permissive =
  False
    (struct
      let module_name = "Permissive"
      let option_name = "-permissive"
      let help =
        "perform less verifications on validity of command-line options"
    end)

[@@@warning "+60"]

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
