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

(* File yalexer.mll *)
{
    open Yaparser
}

let num    = ['0'-'9']
let alpha  = ['a'-'z' 'A'-'Z']
let ident  = alpha (num | alpha | '_')*
let string = ([^ '"' '\\']|'\\'_)*


rule token = parse
    [' ' '\t' ]       { token lexbuf }     (* skip blanks *)
  | '\n'              { Utils_parser.newline lexbuf; token lexbuf }
  | ['0'-'9']+ as lxm { INT(lxm) }
  | "CALL"            { CALL_OF }
  | "RETURN"          { RETURN_OF }
  | "COR"             { CALLORRETURN_OF }
  | "other"           { OTHERWISE }
  | "true"            { TRUE }
  | "false"           { FALSE }
  | "\\result" as lxm { IDENTIFIER(lxm) }
  | ident as lxm      { IDENTIFIER(lxm) }
  | '$' (ident as lxm){ METAVAR(lxm) }
  | ','               { COMMA }
  | '+'               { PLUS }
  | '-'               { MINUS }
  | '*'               { STAR }
  | '/'               { SLASH }
  | '%'               { PERCENT }
  | '('               { LPAREN }
  | ')'               { RPAREN }
  | '['               { LSQUARE }
  | ']'               { RSQUARE }
  | '{'               { LCURLY }
  | '}'               { RCURLY }
  | "{{"              { LBRACELBRACE }
  | "}}"              { RBRACERBRACE }
  | '.'               { DOT }
  | "->"              { RARROW }
  | '&'               { AMP }
  | '|'               { PIPE }
  | "&&"              { AND }
  | "||"              { OR }
  | '!'               { NOT }
  | "<"               { LT }
  | ">"               { GT }
  | "<="              { LE }
  | ">="              { GE }
  | "=="              { EQ }
  | "!="              { NEQ }
  | ';'               { SEMI_COLON }
  | ':'               { COLON }
  | "::"              { COLUMNCOLUMN }
  | '^'               { CARET }
  | '?'               { QUESTION }
  | eof               { EOF }
  | ":="              { AFF }
  | _                 { Utils_parser.unknown_token lexbuf }
