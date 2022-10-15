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

let analyze kf =
  if Kernel_function.is_definition kf
  then
    if Cil_datatype.Stmt.Set.is_empty (Loop.get_non_naturals kf)
    then Loop_analysis.analyze kf
    else
      Options.warning "Could not analyze function %a;@ \
                       it contains a non-natural loop"
        Kernel_function.pretty kf
;;

let main () =
  if Options.Run.get() then begin
    Globals.Functions.iter analyze;
    Loop_analysis.display_results ();
  end
;;

Db.Main.extend main;;
