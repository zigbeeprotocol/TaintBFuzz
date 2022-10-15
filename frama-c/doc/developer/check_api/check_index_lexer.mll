(**************************************************************************)
(*                                                                        *)
(*  This file is part of Frama-C.                                         *)
(*                                                                        *)
(*  Copyright (C) 2007-2021                                               *)
(*    CEA (Commissariat à l'énergie atomique et aux énergies              *)
(*         alternatives)                                                  *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*  Contact CEA LIST for licensing.                                       *)
(*                                                                        *)
(**************************************************************************)

{
}
rule token = parse
| "\\texttt"                               { Check_index_grammar.KWD_WITH_ARG }
| "\\see"                                  { Check_index_grammar.KWD_WITH_ARG }
| "\\fontsize"                     { Check_index_grammar.KWD_WITH_DOUBLE_ARGS }
| [ ' ' '\t' '|' '!' '@' '$' ]             { token lexbuf }
| '{'                                      { Check_index_grammar.LPAR }
| '}'                                      { Check_index_grammar.RPAR }
| [ '\n' '\r' ]                            { Check_index_grammar.EOL }
| "\\indexentry"                           { Check_index_grammar.ENTRY }
(* ignore argument free keywords *)
| "\\selectfont"                           { token lexbuf }
| "hyperpage"                              { token lexbuf }
| "hyperindexformat"                       { token lexbuf }
| "\\bfit"                                 { token lexbuf }
| [ ^ '\n' '\r' ' ' '{' '}' '!' '|' '@' '$' ]*
    { Check_index_grammar.WORD (Lexing.lexeme lexbuf) }
| eof                                      { Check_index_grammar.EOF }
| _ as c                           { Format.eprintf "%c@." c; assert false }

and token_2 = parse
  | '\n'* ' '* [ 'a'-'z' '-' '.' ]+[ ^ '\n' ]*                                              { token_2 lexbuf }
  | '\n'* ' '* ([ 'A'-'Z' ][ 'a'-'z' '-' '_' '.' ]+ ' '* )+ ['A'-'Z'][^ 'a'-'z' '\n']+      { token_2 lexbuf }
  | '\n'* ' '* ([ 'A'-'Z' ][ 'a'-'z' ]+[ ^ '\n' ' ' ]* ' '* )+ ([ 'a'-'z' ]+[ ^ '\n' ' ' ]* ' '* )* as s { if not (String.contains s '.') then Check_index_grammar.STRING (Lexing.lexeme lexbuf) else token_2 lexbuf}
  | '\n'* ' '* [ 'A'-'Z' '_' '-' ]+ [ ^ '\n' ]*                                     { token_2 lexbuf }
  | '\n'* eof                                                                       { Check_index_grammar.EOF }
