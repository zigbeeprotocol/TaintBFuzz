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

(**************************************************************************)
(* Hooks run very early *)
(**************************************************************************)

let print_config () =
  if Kernel.PrintConfig.get () then begin
    Log.print_on_output
      (fun fmt -> Format.fprintf fmt
          "Frama-C %s@\n\
           Environment:@\n  \
           FRAMAC_SHARE  = %S@\n  \
           FRAMAC_LIB    = %S@\n  \
           FRAMAC_PLUGIN = %S%t@."
          Fc_config.version_and_codename
          (Fc_config.datadir:>string) (Fc_config.libdir:>string)
          Fc_config.plugin_path
          (fun fmt ->
             if Fc_config.preprocessor = "" then
               Format.fprintf fmt "@\nWarning: no default pre-processor"
             else if not Fc_config.preprocessor_keep_comments then
               Format.fprintf fmt
                 "@\nWarning: default pre-processor is not able to keep comments \
                  (hence ACSL annotations) in its output")
        ;
      );
    raise Cmdline.Exit
  end
let () = Cmdline.run_after_early_stage print_config

let print_config get value () =
  if get () then begin
    Log.print_on_output (fun fmt -> Format.fprintf fmt "%s%!" value) ;
    raise Cmdline.Exit
  end

let print_version =
  print_config Kernel.PrintVersion.get Fc_config.version_and_codename
let () = Cmdline.run_after_early_stage print_version

let print_sharepath =
  print_config Kernel.PrintShare.get (Fc_config.datadir:>string)
let () = Cmdline.run_after_early_stage print_sharepath

let print_libpath =
  print_config Kernel.PrintLib.get (Fc_config.libdir:>string)
let () = Cmdline.run_after_early_stage print_libpath

let print_pluginpath =
  print_config Kernel.PrintPluginPath.get Fc_config.plugin_path
let () = Cmdline.run_after_early_stage print_pluginpath

(**************************************************************************)
(* Hooks run after loading plug-ins *)
(**************************************************************************)

(* just after loading all plug-ins, add the dependencies between the AST
   and the command line options that depend on it. *)
let () =
  Cmdline.run_after_extended_stage
    (fun () ->
       State_dependency_graph.add_dependencies
         ~from:Ast.self
         !Parameter_builder.ast_dependencies)

(**************************************************************************)
(* Hooks run when restoring a saved file *)
(**************************************************************************)

(* Load Frama-c from disk if required *)
let load_binary () =
  if not (Kernel.LoadState.is_empty ()) then begin
    let filepath = Kernel.LoadState.get () in
    try
      Project.load_all filepath
    with Project.IOError s ->
      Kernel.abort "problem while loading file %a (%s)"
        Filepath.Normalized.pretty filepath s
  end
let () = Cmdline.run_after_loading_stage load_binary

(**************************************************************************)
(* Hooks run when exiting *)
(**************************************************************************)

let print_machdep () =
  if Kernel.PrintMachdep.get () then begin
    File.pretty_machdep ();
    raise Cmdline.Exit
  end else
    Cmdline.nop
let () = Cmdline.run_after_exiting_stage print_machdep

(* Time *)
let time () =
  let filename = Kernel.Time.get () in
  if filename <> "" then
    let oc =
      open_out_gen
        [ Open_append; Open_creat; Open_binary] 0b111100100 filename
    in
    let {Unix.tms_utime = time } = Unix.times () in
    let now = Unix.localtime (Unix.time ()) in
    Printf.fprintf oc "%02d/%02d/%02d %02d:%02d:%02d %f\n"
      now.Unix.tm_mday
      (now.Unix.tm_mon+1)
      (now.Unix.tm_year - 100)
      now.Unix.tm_hour
      now.Unix.tm_min
      now.Unix.tm_sec
      time;
    flush oc;
    close_out oc
let () = Extlib.safe_at_exit time

(* Save Frama-c on disk if required *)
let save_binary error_extension =
  if not (Kernel.SaveState.is_empty ()) then begin
    let filename = Kernel.SaveState.get () in
    Kernel.SaveState.clear ();
    let realname =
      match error_extension with
      | None -> filename
      | Some err_ext ->
        let s = (filename:>string) ^ err_ext in
        Kernel.warning
          "attempting to save on non-zero exit code: \
           modifying filename into `%s'." s;
        Filepath.Normalized.of_string s
    in
    try
      Project.save_all realname
    with Project.IOError s ->
      Kernel.error "problem while saving to file %a (%s)."
        Filepath.Normalized.pretty realname s
  end
let () =
  (* implement a refinement of the behavior described in BTS #1388:
     - on normal exit: save
     - on Sys.break (Ctrl-C interruption): save, but add ".break" suffix
     - on user error: save, but add ".error" suffix
     - on fatal error or unexpected error: save, but add ".crash" suffix *)
  Cmdline.at_normal_exit (fun () -> save_binary None);
  Cmdline.at_error_exit
    (function
      | Sys.Break -> save_binary (Some ".break")
      | Log.AbortError _ | Log.FeatureRequest _ -> save_binary (Some ".error")
      | _ -> save_binary (Some ".crash"))

(* Write JSON files to disk if required *)
let flush_json_files () =
  let written = Json.flush_cache () in
  List.iter (fun fp ->
      Kernel.feedback "Wrote: %a" Filepath.Normalized.pretty fp)
    written

(* Registers an exit hook that flushes Json objects and writes JSON files. This
   hook must be run last (in case other hooks modifiy JSON objects), so it is
   registered after the extended stage, when plug-ins have been loaded. *)
let () =
  Cmdline.run_after_extended_stage
    (fun () -> Cmdline.at_normal_exit (fun () -> flush_json_files ()))

let run_list_all_plugin_options () =
  if not (Kernel.AutocompleteHelp.is_empty ()) then begin
    let filter = Kernel.AutocompleteHelp.get () in
    Plugin.iter_on_plugins
      (fun plugin ->
         if Datatype.String.Set.mem plugin.p_shortname filter then begin
           Format.printf "Plugin: %s@." plugin.Plugin.p_name;
           let plugins_opts = Hashtbl.fold
               (fun group_name group_options acc ->
                  (* note: boolean options with negative counterparts
                     generate 2 strings *)
                  let strings_of_typed_parameter tp =
                    let name = tp.Typed_parameter.name in
                    (* special case due to the "cmdline hack" related to
                       the "Input C files" option: if it does not start
                       with '-', ignore it *)
                    if String.get name 0 <> '-' then []
                    else
                      match tp.Typed_parameter.accessor with
                      | Typed_parameter.Bool (_, opt_neg) ->
                        begin
                          match opt_neg with
                          | None -> [(name, "bool")]
                          | Some neg -> [(name, "bool"); (neg, "bool")]
                        end
                      | Int (_, frange) ->
                        let (min, max) = frange () in
                        if min = min_int && max = max_int then [(name, "int")]
                        else [(name, Format.asprintf "int (%d, %d)" min max)]
                      | String (_, fvalues) ->
                        let values = fvalues () in
                        if values = [] then [(name, "string")]
                        else
                          [(name, Format.asprintf "string (%a)"
                              (Pretty_utils.pp_list ~sep:", "
                                 Format.pp_print_string) values)]
                  in
                  let group_options =
                    List.flatten
                      (List.map strings_of_typed_parameter group_options)
                  in
                  (group_name, group_options) :: acc
               ) plugin.Plugin.p_parameters []
           in
           let plugin_option_strings =
             List.fold_left (fun acc (_gn, go) -> acc @ go) [] plugins_opts
           in
           let cmp_options (n1, _) (n2, _) = String.compare n1 n2 in
           let sorted_options =
             List.sort cmp_options plugin_option_strings
           in
           let pp_option fmt (n, a) = Format.fprintf fmt "  %s: %s@." n a in
           Format.printf "%a" (Pretty_utils.pp_list ~sep:"" pp_option) sorted_options
         end
      );
    raise Cmdline.Exit
  end
  else Cmdline.nop
let () = Cmdline.run_after_exiting_stage run_list_all_plugin_options

(**************************************************************************)
(* Hooks independent from cmdline ordering *)
(**************************************************************************)

let warn_if_another_compiler_builtin name =
  try
    (* Before warning, we must make sure the builtins from other compilers
       are loaded. *)
    if not (Cil_builtins.Gcc_builtin_templates_loaded.get ()) then
      Cil_builtins.init_gcc_builtin_templates ();
    let bt = Cil_builtins.Builtin_templates.find name in
    let compiler = Option.get bt.compiler in
    Kernel.warning ~wkey:Kernel.wkey_implicit_function_declaration
      ~current:true ~once:true
      "%s is a compiler builtin, %s" name
      (Cil.allowed_machdep (Cil_builtins.string_of_compiler compiler));
    true
  with Not_found -> false

(* This hook cannot be registered directly in Kernel or Cabs2cil, as it
   depends on Ast_info *)
let on_call_to_undeclared_function vi =
  let name = vi.Cil_types.vname in
  if not (Ast_info.is_frama_c_builtin name) then begin
    if not (warn_if_another_compiler_builtin name) then
      Kernel.warning ~wkey:Kernel.wkey_implicit_function_declaration
        ~current:true ~once:true
        "Calling undeclared function %s. Old style K&R code?" name
  end

let () =
  Cabs2cil.register_implicit_prototype_hook on_call_to_undeclared_function

(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
