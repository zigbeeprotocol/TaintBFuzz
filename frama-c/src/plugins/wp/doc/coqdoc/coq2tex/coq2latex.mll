(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU General Public License as published by  *)
(*  the Free Software Foundation, either version 2 of the License, or  *)
(*  (at your option) any later version.  This file is also distributed *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

{
open Printf

(** Cross-referencing *)

let current_module = ref ""

type xref =
  | Def of string * string (* path, type *)
  | Ref of string * string * string (* module, name, type *)

let xref_table : (string * int, xref) Hashtbl.t = Hashtbl.create 273
let xref_modules : (string, unit) Hashtbl.t = Hashtbl.create 29

let add_module m =
  Hashtbl.add xref_modules m ()

let add_anchor pos name ty =
  Hashtbl.add xref_table (!current_module,pos) (Def(name,ty))

let add_reference pos library name ty =
  Hashtbl.add xref_table (!current_module,pos) (Ref(library,name,ty))

type link = 
  | URL of string
  | LINK of string
  | LABEL of string 
  | Nolink

let coqlib_url = "http://coq.inria.fr/library/"

let re_coqlib = Str.regexp "Coq\\."
let re_sane_path = Str.regexp "[A-Za-z0-9_.]+$"

let coqlib m p = 
  if p = "" 
  then Printf.sprintf "coq:%s" m 
  else Printf.sprintf "coq:%s:%s" m p

let coqurl lib p =
  if p = "" 
  then Printf.sprintf "%s%s.html" coqlib_url lib
  else Printf.sprintf "%s%s.html#%s" coqlib_url lib p

let crossref m id pos =
  try match Hashtbl.find xref_table (m, pos) with
    | Def(p, ty) -> LABEL (coqlib m p)
    | Ref(lib, p, ty) ->
	if Hashtbl.mem xref_modules lib then
	  LINK (coqlib lib p)
	else if Str.string_match re_coqlib lib 0 then
          URL (coqurl lib p)
	else Nolink
  with Not_found ->
    Nolink

(** Keywords, etc *)

module StringSet = Set.Make(String)

let mkset l = List.fold_right StringSet.add l StringSet.empty

let coq_keywords = mkset [
  "forall"; "match"; "as"; "in"; "return"; "with"; "end"; "let";
  "dest"; "fun"; "if"; "then"; "else"; "Prop"; "Set"; "Type"; ":=";
  "where"; "struct"; "wf"; "measure";
  "AddPath"; "Axiom"; "Abort"; "Boxed"; "Chapter"; "Check";
  "Coercion"; "CoFixpoint"; "CoInductive"; "Corollary"; "Defined";
  "Definition"; "End"; "Eval"; "Example"; "Export"; "Fact"; "Fix";
  "Fixpoint"; "Global"; "Grammar"; "Goal"; "Hint"; "Hypothesis";
  "Hypotheses"; "Resolve"; "Unfold"; "Immediate"; "Extern";
  "Implicit"; "Import"; "Inductive"; "Infix"; "Lemma"; "Let"; "Load";
  "Local"; "Ltac"; "Module"; "Module Type"; "Declare Module";
  "Include"; "Mutual"; "Parameter"; "Parameters"; "Print"; "Proof";
  "Qed"; "Record"; "Recursive"; "Remark"; "Require";
  "Save"; "Scheme"; "Induction"; "for"; "Sort"; "Section"; "Show";
  "Structure"; "Syntactic"; "Syntax"; "Tactic"; "Theorem"; "Set";
  "Types"; "Undo"; "Unset"; "Variable"; "Variables"; "Context";
  "Notation"; "Reserved"; "Tactic"; "Delimit"; "Bind"; "Open";
  "Scope"; "Boxed"; "Unboxed"; "Inline"; "Implicit Arguments"; "Add";
  "Strict"; "Typeclasses"; "Instance"; "Global Instance"; "Class";
  "Instantiation"; "subgoal"; "Program"; "Example"; "Obligation";
  "Obligations"; "Solve"; "using"; "Next"; "Instance"; "Equations";
  "Equations_nocomp"
]

let coq_tactics = mkset [
  "intro"; "intros"; "apply"; "rewrite"; "refine"; "case"; "clear";
  "injection"; "elimtype"; "progress"; "setoid_rewrite"; "destruct";
  "destruction"; "destruct_call"; "dependent"; "elim";
  "extensionality"; "f_equal"; "generalize"; "generalize_eqs";
  "generalize_eqs_vars"; "induction"; "rename"; "move"; "omega";
  "set"; "assert"; "do"; "repeat"; "pose" ; "cut"; "assumption"; "exact";
  "split"; "subst"; "try"; "discriminate"; "simpl"; "unfold"; "red";
  "compute"; "at"; "in"; "by"; "reflexivity"; "symmetry"; 
  "exists" ; "left" ; "right" ;
  "transitivity"; "replace"; "setoid_replace"; "inversion";
  "inversion_clear"; "pattern"; "intuition"; "congruence"; "fail";
  "fresh"; "trivial"; "exact"; "tauto"; "firstorder"; "ring";
  "clapply"; "program_simpl"; "program_simplify"; "eapply"; "auto";
  "eauto"
]

(** HTML generation *)

let oc = ref stdout

let section_level = function
  | "*" -> "subsection"
  | "**" -> "subsubsection"
  | _ -> "paragraph"

let enum_depth = ref 0

let rec set_enum_depth d =
  if !enum_depth < d then begin
    fprintf !oc "\n\\begin{itemize}\n\\item ";
    incr enum_depth;
  end 
  else if !enum_depth > d then begin
    fprintf !oc "\n\\end{itemize}\n";
    decr enum_depth;
  end
  else if !enum_depth > 0 then begin
    fprintf !oc "\n\\item ";
  end

let character = function
  | '#' -> output_string !oc "\\#"
  | '&' -> output_string !oc "\\&"
  | '%' -> output_string !oc "\\%"
  | '\\' -> output_string !oc "{\\textbackslash}"
  | '_' -> output_string !oc "\\_"
  | '^' -> output_string !oc "{\\textasciicircum}"
  | c -> output_char !oc c

let clink = function
  | '#' -> fprintf !oc "\\#"
  | '_' -> fprintf !oc "-"
  | c -> output_char !oc c

let name _ = String.iter character
let link _ = String.iter clink 
    
let ident pos id =
  if StringSet.mem id coq_keywords then
    fprintf !oc "\\coqkw{%a}" name id
  else if StringSet.mem id coq_tactics then
    fprintf !oc "\\coqtac{%a}" name id
  else match crossref !current_module id pos with
    | Nolink ->
	fprintf !oc "\\coqvar{%a}" name id
    | LABEL p ->
	fprintf !oc "\\coqlabel{%a}{\\coqid{%a}}" link p name id
    | LINK p ->
	fprintf !oc "\\coqlink{%a}{\\coqid{%a}}" link p name id
    | URL p ->
	fprintf !oc "\\coqurl{%a}{\\coqid{%a}}" link p name id

let space s = 
  if String.length s > 0 then
    begin
      output_string !oc "\\phantom{" ;
      for i = 1 to String.length s do output_char !oc 'm' done ;
      output_string !oc "}"
    end

let newline () = fprintf !oc "\\\\\n"

let dashes = function
  | "-" -> set_enum_depth 1
  | "--" -> set_enum_depth 2
  | "---" -> set_enum_depth 3
  | "----" -> set_enum_depth 4
  | _ -> fprintf !oc "\n\\hline\n\n"

let coqplain = ref false

let textmode () = 
  if !coqplain then
    ( fprintf !oc "\\end{coqplain}\n" ; coqplain := false )

let coqmode () =
  if not !coqplain then
    ( fprintf !oc "\\begin{coqplain}\n\\par\\noindent" ; coqplain := true )

let start_section sect =
  textmode () ;
  fprintf !oc "\\%s{" (section_level sect)
let end_section () =
  fprintf !oc "}\n"

let start_doc_right () =
  textmode () ;
  fprintf !oc "\\begin{raggedright}\n"
let end_doc_right () =
  fprintf !oc "\\end{raggedright}\n"

let start_bracket () =
  fprintf !oc "\\texttt{"

let end_bracket () =
  fprintf !oc "}"

let start_comment () =
  coqmode () ;
  fprintf !oc "\\begin{coqcomment}(* "

let end_comment () =
  fprintf !oc "*)\\end{coqcomment}"

let admitted () =
  coqmode () ;
  fprintf !oc "\textit{Admitted.}\n"

let start_module modname =
  textmode () ;
  fprintf !oc "\\section{Module %a}\n\\coqlabel{%a}{}\n\n" name modname link modname

let end_module () = 
  textmode ()

}

let space = [' ' '\t']
let ident = ['A'-'Z' 'a'-'z' '_'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*
let path = ident ("." ident)*
let start_proof = "Proof." | ("Proof" space+ "with") | ("Next" space+ "Obligation.")
let end_proof = "Qed." | "Defined." | "Save." | "Admitted." | "Abort."

let sep = space+ "<>"
let xref = ['A'-'Z' 'a'-'z' '0'-'9' '_' '.']+
let trail = space* "\n"
let integer = ['0'-'9']+

rule coq_bol = parse
  | space* "Admitted."
      { admitted () ;
	skip_newline lexbuf }
  | space* start_proof
      { skip_proof lexbuf }
  | space* "(** " ("*"+ as sect)
      { start_section sect;
        doc lexbuf;
        end_section ();
        skip_newline lexbuf }
  | space* "(** "
      { textmode ();
        doc lexbuf;
        skip_newline lexbuf;
      }
  | space* "(*"
      { comment lexbuf ; 
	skip_newline lexbuf }
  | eof
      { () }
  | space* as s
      { space s;
        coq lexbuf }

and skip_proof = parse
  | "Admitted." { admitted () ; newline () ; skip_newline lexbuf }
  | end_proof { skip_newline lexbuf }
  | eof { () }
  | _ { skip_proof lexbuf }

and skip_newline = parse
  | space* "\n"
      { coq_bol lexbuf }
  | space* ""
      { coq lexbuf }

and coq = parse
  | "(**r "
      { start_doc_right();
        doc lexbuf;
        end_doc_right();
        coq lexbuf }
  | "(*"
      { coqmode () ; comment lexbuf; coq lexbuf }
  | path as id
      { coqmode () ; ident (Lexing.lexeme_start lexbuf) id; coq lexbuf }
  | "\n"
      { if !coqplain then newline () else character '\n' ; 
	coq_bol lexbuf }
  | eof
      { () }
  | _ as c
      { coqmode () ; character c; coq lexbuf }

and bracket = parse
  | ']'
      { () }
  | '['
      { character '['; bracket lexbuf; character ']'; bracket lexbuf }
  | path as id
      { ident (Lexing.lexeme_start lexbuf) id; bracket lexbuf }
  | eof
      { () }
  | _ as c
      { character c; bracket lexbuf }

and comment = parse
  | "*)"
      { () }
  | "(*"
      { comment lexbuf; comment lexbuf }
  | eof
      { () }
  | _
      { comment lexbuf }

and coq_comment = parse
  | "*)"
      { () }
  | "(*"
      { start_comment () ; coq_comment lexbuf; end_comment () ;
	coq_comment lexbuf }
  | eof
      { () }
  | _ as c
      { character c ; coq_comment lexbuf }

and doc_bol = parse
  | "<<" space* "\n"
      { coqmode();
        verbatim lexbuf;
        coqmode();
        doc_bol lexbuf }
  | space* ("-"+ as d)
      { textmode () ; dashes d; doc lexbuf }
  | "\n"
      { character '\n' ; set_enum_depth 0; doc_bol lexbuf }
  | ""
      { doc lexbuf }

and doc = parse
  | "*)"
      { () }
  | "\n"
      { character '\n'; doc_bol lexbuf }
  | "["
      { start_bracket(); bracket lexbuf; end_bracket(); doc lexbuf }
  | "$" ([^ '\n' '$']* as latex) "$"
      { output_string !oc latex }
  | "#" [^ '\n' '#']* "#"
      { doc lexbuf }
  | "{!" ([^ ':']+ as name) ':'
      { fprintf !oc "\\coqlink{%s}{" name ; doc lexbuf }
  | "{@" ([^ ':']+ as name) ':'
      { fprintf !oc "\\coqlabel{%s}{" name ; doc lexbuf }
  | "}"
      { fprintf !oc "}" ; doc lexbuf }
  | eof
      { () }
  | _ as c
      { character c; doc lexbuf }

and verbatim = parse
  | "\n>>" space* "\n"
      { () }
  | eof
      { () }
  | _ as c
      { character c; verbatim lexbuf }

and globfile = parse
  | eof
      { () }

  | "F" (ident as m)
        trail

      { current_module := m; add_module m;
        globfile lexbuf }

  | "R" (integer as pos) ':' integer 
        space+ (xref as library) sep sep space+ "lib" 
	trail

      { add_reference (int_of_string pos) library "" "lib" ;
	globfile lexbuf }
	
  | "R" (integer as pos) ':' integer
        space+ (xref as library) sep
	space+ (ident as name)
	space+ (ident as ty)
	trail

      { add_reference (int_of_string pos) library name ty ;
        globfile lexbuf }

  | (ident as ty)
        space+ (integer as pos) ':' integer
        sep space+ (ident as name) trail

      { add_anchor (int_of_string pos) name ty;
        globfile lexbuf }

  | [^ '\n']* "\n"
      { globfile lexbuf }

{

let output_name = ref "-"

let process_file f =
  if Filename.check_suffix f ".v" then begin
    current_module := Filename.chop_suffix (Filename.basename f) ".v";
    let ic = open_in f in
    if !output_name = "-" then
      oc := stdout
    else
      (oc := open_out (Str.global_replace (Str.regexp "%") !current_module
                                                           !output_name)) ;
    start_module !current_module;
    coq_bol (Lexing.from_channel ic);
    end_module () ;
    if !output_name <> "-" then (close_out !oc; oc := stdout);
    close_in ic
  end else
    if Filename.check_suffix f ".glob" then begin
      current_module := "";
      let ic = open_in f in
      globfile (Lexing.from_channel ic);
      close_in ic
    end else begin
      eprintf "Don't know what to do with file %s\n" f;
      exit 2
    end
      
let _ =
  Arg.parse [
    "-o", Arg.String (fun s -> output_name := s),
    " <output>   Set output file ('%' replaced by module name)"
  ] process_file
    "Usage: coq2latex [options] <file.glob> file.v\nOptions are:"
}
