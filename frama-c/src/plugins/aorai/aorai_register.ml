(**************************************************************************)
(*                                                                        *)
(*  This file is part of Aorai plug-in of Frama-C.                        *)
(*                                                                        *)
(*  Copyright (C) 2007-2022                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*    INRIA (Institut National de Recherche en Informatique et en         *)
(*           Automatique)                                                 *)
(*    INSA  (Institut National des Sciences Appliquees)                   *)
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

open Logic_ptree
open Promelaast

(* [VP] Need to get rid of those global references at some point. *)
let promela_file = ref Filepath.Normalized.empty
let c_file = ref Filepath.Normalized.empty
let ltl_tmp_file = ref Filepath.Normalized.empty
let ltl_file = ref Filepath.Normalized.empty
let dot_file = ref Filepath.Normalized.empty
let ltl2ba_params = " -l -p -o "

let ltl_to_promela = Hashtbl.create 7

let set_ltl_correspondence h =
  Hashtbl.clear ltl_to_promela;
  Hashtbl.iter (fun x y -> Hashtbl.add ltl_to_promela x y) h

let convert_ltl_exprs t =
  let rec convert_cond cond =
    match cond with
      POr(c1,c2) -> POr (convert_cond c1, convert_cond c2)
    | PAnd(c1,c2) -> PAnd(convert_cond c1, convert_cond c2)
    | PNot c -> PNot (convert_cond c)
    | PCall _ | PReturn _ | PTrue | PFalse -> cond
    | PRel(Neq,PVar x,PCst _) ->
      (try
         let (rel,t1,t2) = Hashtbl.find ltl_to_promela x in PRel(rel,t1,t2)
       with Not_found -> cond)
    | PRel _ -> cond
  in
  let rec convert_seq_elt e =
    { e with
      condition = Option.map convert_cond e.condition;
      nested = convert_seq e.nested; }
  and convert_seq s = List.map convert_seq_elt s in
  let convert_parsed c =
    match c with
      Seq l -> Seq (convert_seq l)
    | Otherwise -> Otherwise
  in
  let convert_trans t = { t with cross = convert_parsed t.cross } in
  List.map convert_trans t

(* Promela file *)

(* Performs some checks before calling [open_in f], reporting ["errmsg: <f>"]
   in case of error. *)
let check_and_open_in (f : Filepath.Normalized.t) errmsg =
  if not (Filepath.Normalized.is_file f) then
    Aorai_option.abort "%s: %a" errmsg Filepath.Normalized.pretty f;
  open_in (f :> string)

let ltl_to_ltlLight f_ltl (f_out : Filepath.Normalized.t) =
  let c = check_and_open_in f_ltl "invalid LTL file" in
  let (ltl_form,exprs) = Ltllexer.parse c in
  close_in c;
  Ltl_output.output ltl_form (f_out :> string);
  set_ltl_correspondence exprs

let load_ya_file filename  =
  let channel = check_and_open_in filename "invalid Ya file" in
  let lexbuf = Lexing.from_channel channel in
  Lexing.(lexbuf.lex_curr_p <-
            { lexbuf.lex_curr_p with pos_fname = (filename :> string) });
  try
    let automata = Yaparser.main Yalexer.token lexbuf in
    close_in channel;
    Data_for_aorai.setAutomata automata
  with
  | Parsing.Parse_error ->
    Utils_parser.abort_current lexbuf "syntax error"

let load_promela_file f  =
  let c = check_and_open_in f "invalid Promela file" in
  let auto = Promelalexer.parse c  in
  let trans = convert_ltl_exprs auto.trans in
  close_in c;
  Data_for_aorai.setAutomata { auto with trans }

let load_promela_file_withexps f =
  let c = check_and_open_in f "invalid Promela file" in
  let automata = Promelalexer_withexps.parse c  in
  close_in c;
  Data_for_aorai.setAutomata automata

let display_status () =
  if Aorai_option.verbose_atleast 2 then begin
    Aorai_option.feedback "\n"  ;
    Aorai_option.feedback "C file:            '%a'\n" Filepath.Normalized.pretty !c_file ;
    Aorai_option.feedback "Entry point:       '%a'\n"
      Kernel_function.pretty (fst (Globals.entry_point())) ;
    Aorai_option.feedback "LTL property:      '%a'\n" Filepath.Normalized.pretty !ltl_file ;
    if Aorai_option.Dot.get () then
      Aorai_option.feedback "Dot file:          '%a'\n" Filepath.Normalized.pretty !dot_file;
    Aorai_option.feedback "Tmp files:         '%a' (Light LTL file)\n"
      Filepath.Normalized.pretty !ltl_tmp_file ;
    Aorai_option.feedback "                   '%a' (Promela file)\n"
      Filepath.Normalized.pretty !promela_file ;
    Aorai_option.feedback "\n"
  end

let init_file_names () =
  let freshname ?opt_suf file suf =
    let name = (file:Filepath.Normalized.t:>string) in
    let pre = Filename.remove_extension name in
    let pre = match opt_suf with None -> pre | Some s -> pre ^ s in
    let rec fn p s n =
      if not (Sys.file_exists (p^(string_of_int n)^s)) then (p^(string_of_int n)^s)
      else fn p s (n+1)
    in
    let name =
      if not (Sys.file_exists (pre^suf)) then pre^suf
      else fn pre suf 0
    in
    Filepath.Normalized.of_string name
  in
  if Aorai_option.Ya.is_empty () then
    if Aorai_option.Buchi.is_empty () then begin
      (* ltl_file name is given and has to point out a valid file. *)
      ltl_file := Aorai_option.Ltl_File.get ();
      if Aorai_option.Dot.get() then dot_file := freshname !ltl_file ".dot";
      (* The LTL file is always used. *)
      (* The promela file can be given or not. *)
      if not (Aorai_option.To_Buchi.is_empty ()) then begin
        ltl_tmp_file:=
          freshname (Aorai_option.promela_file ()) ".ltl";
        promela_file:= Aorai_option.promela_file ();
        Extlib.cleanup_at_exit (!ltl_tmp_file :> string)
      end else begin
        ltl_tmp_file:=
          (try
             Filepath.Normalized.of_string
               (Extlib.temp_file_cleanup_at_exit
                  (Filename.basename (!c_file:>string)) ".ltl")
           with Extlib.Temp_file_error s ->
             Aorai_option.abort "cannot create temporary file: %s" s);
        promela_file:=
          freshname !ltl_tmp_file ".promela";
        Extlib.cleanup_at_exit (!promela_file :> string);
      end
    end else begin
      if not (Aorai_option.To_Buchi.is_empty ()) && not (Aorai_option.Ltl_File.is_empty ())
      then begin
        Aorai_option.abort
          "Error. '-buchi' option is incompatible with '-to-buchi' and '-ltl' \
           options."
      end;
      (* The promela file is used only if the process does not terminate after
          LTL generation. *)
      promela_file := Aorai_option.promela_file ();
      if Aorai_option.Dot.get() then
        dot_file := freshname !promela_file ".dot";
    end
  else begin
    if Aorai_option.Ya.is_empty () then
      Aorai_option.abort "empty Ya file name";
    if Aorai_option.Dot.get() then
      dot_file := freshname (Aorai_option.Ya.get ()) ".dot"
  end;
  display_status ()

let printverb s = Aorai_option.feedback ~level:2 "%s" s

let output () =
  (* Dot file *)
  if (Aorai_option.Dot.get()) then
    begin
      Promelaoutput.Typed.output_dot_automata (Data_for_aorai.getAutomata ())
        (!dot_file:>string);
      printverb "Generating dot file    : done\n"
    end

let work () =
  let file = Ast.get () in
  Aorai_utils.initFile file;
  printverb "C file loading         : done\n";
  if Aorai_option.Ya.is_empty () then
    if Aorai_option.Buchi.is_empty () then begin
      ltl_to_ltlLight !ltl_file !ltl_tmp_file;
      printverb "LTL loading            : done\n";
      let cmd = Format.asprintf "ltl2ba %s -F %a > %a"
          ltl2ba_params
          Filepath.Normalized.pretty !ltl_tmp_file
          Filepath.Normalized.pretty !promela_file
      in if Sys.command cmd <> 0 then
        Aorai_option.abort "failed to run: %s" cmd ;
      printverb "LTL ~> Promela (ltl2ba): done\n"
    end;
  if not (Aorai_option.To_Buchi.is_empty ()) then
    printverb ("Finished.\nGenerated file: '"^(Filepath.Normalized.to_pretty_string !promela_file)^"'\n")
  else
    begin
      (* Step 3 : Loading promela_file and checking the consistency between informations from C code and LTL property *)
      (*          Such as functions name and global variables. *)

      if not (Aorai_option.Buchi.is_empty ()) then
        load_promela_file_withexps !promela_file
      else if not (Aorai_option.Ya.is_empty ()) then
        load_ya_file (Aorai_option.Ya.get ())
      else
        load_promela_file !promela_file;
      printverb "Loading promela        : done\n";

      (* Promelaoutput.print_raw_automata (Data_for_aorai.getAutomata());  *)
      (* Data_for_aorai.debug_ltl_expressions (); *)

      (*let _ = Path_analysis.test (Data_for_aorai.getAutomata())in*)
      let root = fst (Globals.entry_point ()) in
      let axiomatization = Aorai_option.Axiomatization.get() in
      if axiomatization then
        begin
          (* Step 5 : incrementing pre/post
             conditions with states and transitions information *)
          printverb "Refining pre/post      : \n";
          Aorai_dataflow.compute ();
          (* Step 6 : Removing transitions never crossed *)
          let automaton_has_states =
            if (Aorai_option.AutomataSimplification.get()) then
              begin
                printverb "Removing unused trans  : done\n";
                try
                  Data_for_aorai.removeUnusedTransitionsAndStates ();
                  true
                with Data_for_aorai.Empty_automaton ->
                  Aorai_option.warning
                    "No state of the automaton is reachable. \
                     Program and specification are incompatible, \
                     instrumentation will not be generated.";
                  false
              end
            else
              (printverb "Removing unused trans  : skipped\n"; true)
          in
          if automaton_has_states then begin
            (* Step 7 : Labeling abstract file *)
            (* Finally the information is added into the Cil automata. *)
            Aorai_utils.initGlobals root axiomatization;
            Aorai_visitors.add_sync_with_buch file;
            if Aorai_option.GenerateAnnotations.get () then
              Aorai_visitors.add_pre_post_from_buch file
                (Aorai_option.advance_abstract_interpretation ())
            else if Aorai_option.ConsiderAcceptance.get () then begin
              let kf,_ = Globals.entry_point() in
              let bhv = Aorai_utils.mk_acceptance_bhv () in
              Annotations.add_behaviors Aorai_option.emitter kf [bhv]
            end;
            Aorai_eva_analysis.setup ();
            printverb "Annotation of Cil      : done\n";
          end
        end
      else
        begin
          (* Step 4': Computing the set of possible pre-states and post-states of each function *)
          (*          And so for pre/post transitions *)
          printverb "Abstracting pre/post   : skipped\n";

          (* Step 5': incrementing pre/post conditions with states and transitions information *)
          printverb "Refining pre/post      : skipped\n";


          (* Step 6 : Removing transitions never crossed *)
          printverb "Removing unused trans  : skipped\n";

          (* Step 7 : Labeling abstract file *)
          (* Finally the information is added into the Cil automata. *)
          Aorai_utils.initGlobals root axiomatization;
          Aorai_visitors.add_sync_with_buch file;
          printverb "Annotation of Cil      : partial\n"
        end;

      (* Step 8 : clearing tables whose information has been
         invalidated by our transformations.
      *)
      Ast.mark_as_changed();
      Cfg.clearFileCFG ~clear_id:false file;
      Cfg.computeFileCFG file;
      Ast.clear_last_decl ();
      if Kernel.Check.get() then Filecheck.check_ast "aorai";
      output ()
    end

let run () =
  (* Step 1 : Capture files names *)
  init_file_names ();
  (* Step 2 : Work in our own project, initialized by a copy of the main
     one. *)
  let work_prj =
    File.create_project_from_visitor "aorai"
      (fun prj -> new Visitor.frama_c_copy prj)
  in
  Project.copy ~selection:(Parameter_state.get_selection ()) work_prj;
  Project.on work_prj work ()

(* Plugin registration *)

let run =
  Dynamic.register
    ~plugin:"Aorai"
    "run"
    (Datatype.func Datatype.unit Datatype.unit)
    ~journalize:true
    run

let run, _ =
  State_builder.apply_once
    "Aorai"
    (let module O = Aorai_option in
     [ O.Ltl_File.self; O.To_Buchi.self; O.Buchi.self;
       O.Ya.self; O.Axiomatization.self; O.ConsiderAcceptance.self;
       O.AutomataSimplification.self; O.AbstractInterpretation.self;
       O.AddingOperationNameAndStatusInSpecification.self ])
    run

let main () = if Aorai_option.is_on () then run ()
let () = Db.Main.extend main


(*
Local Variables:
compile-command: "make -C ../../.."
End:
*)
