(* Small script to test that the code generated by aorai can be parsed again
 * by frama-c.
*)

open Kernel

module P = Plugin.Register
    (struct
      let name = "aorai testing module"
      let shortname = "aorai-test"
      let help = "utility script for aorai regtests"
    end)

module TestNumber =
  P.Zero
    (struct
      let option_name = "-aorai-test-number"
      let help = "test number when multiple tests are run over the same file"
      let arg_name = "n"
    end)

module InternalWpShare =
  P.Filepath(
  struct
    let option_name = "-aorai-test-wp-share"
    let help = "use custom wp share dir (when in internal plugin mode)"
    let arg_name = "dir"
    let existence = Filepath.Must_exist
    let file_kind = "wp share directory"
  end)

module ProveAuxSpec =
  P.False(
  struct
    let option_name = "-aorai-test-prove-aux-spec"
    let help = "use WP + alt-ergo to prove that generated spec and body \
                of auxiliary automata functions match"
  end)

let ok = ref false

let is_suffix suf str =
  let lsuf = String.length suf in
  let lstr = String.length str in
  if lstr <= lsuf then false
  else
    let estr = String.sub str (lstr - lsuf) lsuf in
    estr = suf

let extend () =
  let myrun =
    let run = !Db.Toplevel.run in
    fun f ->
      let my_project = Project.create "Reparsing" in
      let wp_compute_kf kf =
        let vcs = Wp.VC.generate_kf kf in
        Wp.VC.command vcs;
        Bag.iter
          (fun vc ->
             if not (Wp.VC.is_proved vc) then
               P.warning "Could not prove %a in automaton function %a"
                 Property.pretty (Wp.VC.get_property vc)
                 Kernel_function.pretty kf)
          vcs
      in
      let check_auto_func kf =
        let name = Kernel_function.get_name kf in
        if Kernel_function.is_definition kf &&
           (is_suffix "_pre_func" name || is_suffix "_post_func" name)
        then
          wp_compute_kf kf
      in
      run f;
      let tmpdir = Filename.get_temp_dir_name () in
      let tmpdir =
        match Filename.chop_suffix_opt ~suffix:"/" tmpdir with
        | None -> tmpdir
        | Some dir -> dir
      in
      let tmpfile =
        tmpdir ^ "/aorai_" ^
        Filename.(
          chop_extension (basename (List.hd (Kernel.Files.get()):>string))) ^
        "_" ^ (string_of_int (TestNumber.get ())) ^ ".i"
      in
      let () =
        Extlib.safe_at_exit
          (fun () ->
             if Debug.get () >= 1 || not !ok then
               result "Keeping temp file %s" tmpfile
             else Extlib.safe_remove tmpfile)
      in
      let chan = open_out tmpfile in
      let fmt = Format.formatter_of_out_channel chan in
      let aorai_prj = Project.from_unique_name "aorai" in
      Project.on aorai_prj Kernel.PrintLibc.on ();
      File.pretty_ast ~prj:aorai_prj ~fmt ();
      close_out chan;
      let selection =
        List.fold_left
          (fun selection state ->
             State_selection.union
               (State_selection.with_codependencies state) selection)
          State_selection.empty
          [ InternalWpShare.self; ProveAuxSpec.self;
            Wp.Wp_parameters.CacheEnv.self;
            Wp.Wp_parameters.Verbose.self;
          ]
      in
      Project.copy ~selection my_project;
      Project.set_current my_project;
      Kernel.SymbolicPath.add
        (Filepath.Normalized.of_string (Filename.get_temp_dir_name ()),
         Some "TMPDIR");
      Files.append_after [ Filepath.Normalized.of_string tmpfile ];
      Kernel.LogicalOperators.on ();
      Constfold.off ();
      Ast.compute();
      if ProveAuxSpec.get () then begin
        if InternalWpShare.is_set() then
          Wp.Wp_parameters.Share.set (InternalWpShare.get());
        Wp.Wp_parameters.Let.off();
        Wp.Wp_parameters.Split.on();
        Wp.Wp_parameters.SplitMax.set 32;
        if not (Wp.Wp_parameters.Verbose.is_set()) then
          Wp.Wp_parameters.Verbose.set 0;
        Globals.Functions.iter check_auto_func;
      end else begin
        File.pretty_ast ();
      end;
      ok:=true (* no error, we can erase the file *)
  in
  Db.Toplevel.run := myrun

let () = extend ()
