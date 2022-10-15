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

(* $Id: promelalexer_withexps.mll,v 1.2 2008-10-02 13:33:29 uid588 Exp $ *)

(* from http://www.ltl2dstar.de/down/ltl2dstar-0.4.2.zip *)

{
  open Promelaparser_withexps
  open Lexing

}




let rD =        ['0'-'9']
let rL = ['a'-'z' 'A'-'Z' '_']


rule token = parse
  | "true"                  { PROMELA_TRUE }
  | "never"                 { PROMELA_NEVER }
  | "if"                    { PROMELA_IF }
  | "fi"                    { PROMELA_FI }
  | "goto"                  { PROMELA_GOTO }
  | "skip"                  { PROMELA_SKIP }
  | "::"                    { PROMELA_DOUBLE_COLON }
  | ':'                     { PROMELA_COLON }
  | ';'                     { PROMELA_SEMICOLON }
  | "()"                    { PROMELA_FUNC }
  | '('                     { PROMELA_LPAREN }
  | ')'                     { PROMELA_RPAREN }
  | '{'                     { PROMELA_LBRACE }
  | '}'                     { PROMELA_RBRACE }
  | "->"                    { PROMELA_RIGHT_ARROW }
  | "false"                 { PROMELA_FALSE }
  | "||"                    { PROMELA_OR }
  | "&&"                    { PROMELA_AND }
  | '!'                     { PROMELA_NOT }
  | [' ' '\t' '\012' '\r']+ { token lexbuf }
  | '\n'                    { Utils_parser.newline lexbuf; token lexbuf }
  | "/*"                    { comment lexbuf; token lexbuf }
  | "//" [^ '\n']* '\n'     { Utils_parser.newline lexbuf; token lexbuf }

  | "callof_" rL* (rL | rD)*
                            { let s=(lexeme lexbuf) in
                              let s=String.sub s 7 ((String.length s)-7) in
                              PROMELA_CALLOF s }
  | "returnof_" rL* (rL | rD)*
                            { let s=(lexeme lexbuf) in
                              let s=String.sub s 9 ((String.length s)-9) in
                              PROMELA_RETURNOF s }
  | "callorreturnof_" rL* (rL | rD)*
                            { let s=(lexeme lexbuf) in
                              let s=String.sub s 15 ((String.length s)-15) in
                              PROMELA_CALLORRETURNOF s }


  | "callof_"               { Utils_parser.abort_current lexbuf
                                "Illegal function name in Promela file." }
  | "returnof_"             { Utils_parser.abort_current lexbuf
                                "Illegal function name in Promela file." }
  | "callorreturnof_"       { Utils_parser.abort_current lexbuf
                                "Illegal function name in Promela file." }


  | rD+ | '-' rD+           { PROMELA_INT (lexeme lexbuf) }


(* Logic relations *)
  | "=="                    { PROMELA_EQ }
  | "<"                     { PROMELA_LT }
  | ">"                     { PROMELA_GT }
  | "<="                    { PROMELA_LE }
  | ">="                    { PROMELA_GE }
  | "!="                    { PROMELA_NEQ }

(* Arithmetic relations *)
  | '+'                     { PROMELA_PLUS }
  | '-'                     { PROMELA_MINUS }
  | '/'                     { PROMELA_DIV }
  | '*'                     { PROMELA_STAR }
  | '%'                     { PROMELA_MODULO}

(* Access *)
(*  | "->"                  { LTL_RIGHT_ARROW }*)
  | '.'                     { PROMELA_DOT }
  | '['                     { PROMELA_LEFT_SQUARE}
  | ']'                     { PROMELA_RIGHT_SQUARE}
(*  | '&'                     { PROMELA_ADRESSE }*)




  | rL (rL | rD)*           { let s = lexeme lexbuf in
                                PROMELA_LABEL s }
  | eof                     { EOF }

  | "1"                     { PROMELA_TRUE }
  | _                       { Utils_parser.unknown_token lexbuf }

and comment = parse
  | "*/" { () }
  | eof  { Aorai_option.abort "Unterminated_comment\n" }
  | '\n' { Utils_parser.newline lexbuf; comment lexbuf }
  | _    { comment lexbuf }


{
  let parse c =
    let lb = from_channel c in
    try
      Promelaparser_withexps.promela token lb
    with
        Parsing.Parse_error -> Utils_parser.abort_current lb "Syntax error"
}
