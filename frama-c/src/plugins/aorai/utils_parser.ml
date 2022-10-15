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

open Lexing

let current_loc lex = Cil_datatype.Position.of_lexing_pos (lexeme_start_p lex)

let abort_current lex fmt =
  let source = current_loc lex in
  let start_line = source.Filepath.pos_lnum in
  let fmt = "before or at token %s@\n%a@\n" ^^ fmt in
  Aorai_option.abort ~source fmt
    (Lexing.lexeme lex)
    (Errorloc.pp_context_from_file ~start_line ~ctx:2) source

let unknown_token lex =
  abort_current lex
    "Unexpected character: '%c'" (lexeme_char lex (lexeme_start lex))

let newline lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }
