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

(* $Id: ltllexer.mll,v 1.2 2008-10-02 13:33:29 uid588 Exp $ *)

(* from http://www.ltl2dstar.de/down/ltl2dstar-0.4.2.zip *)

{
open Ltlparser
open Lexing
}

let rD =        ['0'-'9']
let rL = ['a'-'z' 'A'-'Z' '_']


rule token = parse
  | "true"                  { LTL_TRUE }
  | "false"                 { LTL_FALSE }
  | '('                     { LTL_LPAREN }
  | ')'                     { LTL_RPAREN }

(* Logic operators *)
  | "=>"                    { LTL_IMPLIES }
  | "<=>"                   { LTL_LEFT_RIGHT_ARROW }
  | "||"                    { LTL_OR }
  | "&&"                    { LTL_AND }
  | '!'                     { LTL_NOT }
  | "_G_"                   { LTL_GLOBALLY }
  | "_F_"                   { LTL_FATALLY }
  | "_U_"                   { LTL_UNTIL }
  | "_R_"                   { LTL_RELEASE }
  | "_X_"                   { LTL_NEXT }


(* Logic relations *)
  | "=="                    { LTL_EQ }
  | "<"                     { LTL_LT }
  | ">"                     { LTL_GT }
  | "<="                    { LTL_LE }
  | ">="                    { LTL_GE }
  | "!="                    { LTL_NEQ }

(* Arithmetic relations *)
  | '+'                     { LTL_PLUS }
  | '-'                     { LTL_MINUS }
  | '/'                     { LTL_DIV }
  | '*'                     { LTL_STAR }
  | '%'                     { LTL_MODULO}

(* Access *)
  | "->"                    { LTL_RIGHT_ARROW }
  | '.'                     { LTL_DOT }
  | '['                     { LTL_LEFT_SQUARE}
  | ']'                     { LTL_RIGHT_SQUARE}
  | '&'                     { LTL_ADRESSE }
  | "CALL"                  { LTL_CALL }
  | "RETURN"                { LTL_RETURN }
  | "CALL_OR_RETURN"        { LTL_CALL_OR_RETURN }

(* Comments *)
  | "/*"                    { comment lexbuf; token lexbuf }
  | "//" [^ '\n']* '\n'     { Utils_parser.newline lexbuf; token lexbuf }

(* Spaces *)
  | [' ' '\t' '\012' '\r']+ { token lexbuf }
  | '\n'                    { Utils_parser.newline lexbuf; token lexbuf }

(* Variables and constants *)
  | rD+ | '-' rD+           { LTL_INT (lexeme lexbuf) }
  | rL (rL | rD)*           { LTL_LABEL (lexeme lexbuf) }

(* Others *)
  | eof                     { EOF }
  | _                       { Utils_parser.unknown_token lexbuf }

and comment = parse
  | "*/" { () }
  | eof  { Utils_parser.abort_current lexbuf "Unterminated_comment" }
  | '\n' { Utils_parser.newline lexbuf; comment lexbuf }
  | _    { comment lexbuf }


{
  let parse c =
    let lb = from_channel c in
    try
      Ltlparser.ltl token lb
    with
        Parsing.Parse_error -> Utils_parser.abort_current lb "Syntax error"
}
