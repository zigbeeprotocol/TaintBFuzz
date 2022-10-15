(**************************************************************************)
(*                                                                        *)
(*  This file is part of the Frama-C's E-ACSL plug-in.                    *)
(*                                                                        *)
(*  Copyright (C) 2012-2021                                               *)
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

let analyses_feedback msg =
  Options.feedback ~level:2 "%s in %a" msg Project.pretty (Project.current ())

let preprocess () =
  let ast = Ast.get () in
  analyses_feedback "preprocessing annotations";
  Logic_normalizer.preprocess ast;
  analyses_feedback "normalizing quantifiers";
  Bound_variables.preprocess ast;
  analyses_feedback "typing annotations";
  Typing.type_program ast;
  analyses_feedback
    "computing future locations of labeled predicates and terms";
  Labels.preprocess ast

let reset () =
  Memory_tracking.reset ();
  Literal_strings.reset ();
  Bound_variables.clear_guards ();
  Logic_normalizer.clear ();
  Interval.Env.clear();
  Typing.clear ();
  Labels.reset ()
