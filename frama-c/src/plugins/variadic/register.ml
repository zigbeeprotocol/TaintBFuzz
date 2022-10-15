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

open Cil_types

let category = File.register_code_transformation_category "variadic"

(* Variadic will create prototype and specifications for some variadic
   functions. Since only prototypes are created, the resulting source code isn't
   compilable. This printer will print the original functions, with the replaced
   prototypes in comments beside the instruction. *)
let change_printer =
  let first = ref true in
  fun () ->
    if !first then begin
      first := false;
      let module Printer_class(X: Printer.PrinterClass) = struct
        class printer = object
          inherit X.printer as super

          method !instr fmt i =
            match i with
            (* If the instruction calls a function that have been replaced,
               then build an instruction with the old function. *)
            | Call(res, ({ enode = Lval(Var vi, o) } as fct), args, loc)
              when Replacements.mem vi ->
              let old_vi = Replacements.find vi in
              let old_vi = { vi with vname = old_vi.vname } in
              let old_instr =
                Call(res, { fct with enode = Lval(Var old_vi, o) }, args, loc)
              in
              Format.fprintf fmt "%a /* %s */" super#instr old_instr vi.vname
            (* Otherwise keep the instruction. *)
            | _ ->
              super#instr fmt i
        end
      end in
      Printer.update_printer (module Printer_class: Printer.PrinterExtension)
    end

let () =
  Cmdline.run_after_extended_stage
    begin fun () ->
      State_dependency_graph.add_dependencies
        ~from:Options.Enabled.self
        [ Ast.self ]
    end;
  Cmdline.run_after_configuring_stage
    begin fun () ->
      let translate file =
        if Options.Enabled.get () then begin
          change_printer ();
          Translate.translate_variadics file
        end
      in
      File.add_code_transformation_before_cleanup category translate
    end
