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

let () = Plugin.is_share_visible ()
module P = Plugin.Register
    (struct
      let name = "E-ACSL"
      let shortname = "e-acsl"
      let help = "Executable ANSI/ISO C Specification Language --- runtime \
                  assertion checker generator"
    end)
include P

module Run =
  False
    (struct
      let option_name = "-e-acsl"
      let help = "generate a new project where E-ACSL annotations are \
                  translated to executable C code"
    end)

module Project_name =
  String
    (struct
      let option_name = "-e-acsl-project"
      let help = "the name of the generated project is <prj> \
                  (default to \"e-acsl\")"
      let default = "e-acsl"
      let arg_name = "prj"
    end)

module Valid =
  False
    (struct
      let option_name = "-e-acsl-valid"
      let help = "translate annotation which have been proven valid"
    end)

module Gmp_only =
  False
    (struct
      let option_name = "-e-acsl-gmp-only"
      let help = "always use GMP integers instead of C integral types"
    end)

module Temporal_validity =
  False
    (struct
      let option_name = "-e-acsl-temporal-validity"
      let help = "enable temporal analysis in valid annotations"
    end)

module Validate_format_strings =
  False
    (struct
      let option_name = "-e-acsl-validate-format-strings"
      let help = "enable runtime validation of stdio.h format functions"
    end)

module Replace_libc_functions =
  False
    (struct
      let option_name = "-e-acsl-replace-libc-functions"
      let help = "replace some libc functions (such as strcpy) with built-in\
                  RTL alternatives"
    end)

module Full_mtracking =
  False
    (struct
      let option_name = "-e-acsl-full-mtracking"
      let help = "maximal memory-related instrumentation"
    end)
let () = Full_mtracking.add_aliases ~deprecated:true [ "-e-acsl-full-mmodel" ]

module Builtins =
  String_set
    (struct
      let option_name = "-e-acsl-builtins"
      let arg_name = ""
      let help = "C functions which can be used in the E-ACSL specifications"
    end)

module Assert_print_data =
  True
    (struct
      let option_name = "-e-acsl-assert-print-data"
      let help = "print data contributing to the failed assertion along with \
                  the runtime error message"
    end)

module Concurrency =
  False
    (struct
      let option_name = "-e-acsl-concurrency"
      let help = "activate the concurrency support of E-ACSL. The option \
                  implies -e-acsl-full-mtracking."
    end)

module Functions =
  Kernel_function_set
    (struct
      let option_name = "-e-acsl-functions"
      let arg_name = "f1, ..., fn"
      let help = "only annotations in functions f1, ..., fn are checked at \
                  runtime"
    end)

module Instrument =
  Kernel_function_set
    (struct
      let option_name = "-e-acsl-instrument"
      let arg_name = "f1, ..., fn"
      let help = "only instrument functions f1, ..., fn. \
                  Be aware that runtime verdicts may become partial."
    end)


let () = Parameter_customize.set_group help
module Version =
  False
    (struct
      let option_name = "-e-acsl-version"
      let help = "version of plug-in E-ACSL"
    end)

let version () =
  if Version.get () then begin
    Log.print_on_output
      (fun fmt ->
         Format.fprintf
           fmt
           "Version of plug-in E-ACSL: %s@?"
           Local_config.version);
    raise Cmdline.Exit
  end
let () = Cmdline.run_after_configuring_stage version

let parameter_states =
  [ Valid.self;
    Gmp_only.self;
    Full_mtracking.self;
    Builtins.self;
    Temporal_validity.self;
    Validate_format_strings.self;
    Functions.self;
    Instrument.self ]

let emitter =
  Emitter.create
    "E_ACSL"
    [ Emitter.Code_annot; Emitter.Funspec ]
    ~correctness:[ Functions.parameter;
                   Instrument.parameter;
                   Validate_format_strings.parameter;
                   Temporal_validity.parameter ]
    ~tuning:[ Gmp_only.parameter;
              Valid.parameter;
              Replace_libc_functions.parameter;
              Full_mtracking.parameter ]

let must_visit () = Run.get ()

module Dkey = struct
  let prepare = register_category "preparation"
  let logic_normalizer = register_category "analysis:logic_normalizer"
  let bound_variables = register_category "analysis:bound_variables"
  let interval = register_category "analysis:interval_inference"
  let mtracking = register_category "analysis:memory_tracking"
  let typing = register_category "analysis:typing"
  let labels = register_category "analysis:labels"
  let translation = register_category "translation"
end

let setup ?(rtl=false) () =
  (* Variadic translation *)
  if Plugin.is_present "variadic" then begin
    let opt_name = "-variadic-translation" in
    if Dynamic.Parameter.Bool.get opt_name () then begin
      if rtl then
        (* If we are translating the RTL project, then we need to deactivate the
           variadic translation. Indeed since we are translating the RTL in
           isolation, we do not now if the variadic functions are used by the
            user project and we cannot monomorphise them accordingly. *)
        Dynamic.Parameter.Bool.off opt_name ()
      else if Validate_format_strings.get () then begin
        if Ast.is_computed () then
          abort
            "The variadic translation is incompatible with E-ACSL option \
             '%s'.@ Please use option '-variadic-no-translation'."
            Validate_format_strings.option_name;
        warning ~once:true "deactivating variadic translation";
        Dynamic.Parameter.Bool.off opt_name ();
      end
    end
  end;
  (* Concurrency support *)
  if Concurrency.get () then begin
    if Full_mtracking.is_set () && not (Full_mtracking.get ()) then
      abort
        "The memory tracking dataflow analysis is incompatible@ \
         with the concurrency support of E-ACSL.@ \
         Please use option '-e-acsl-full-mtracking'.";
    if not rtl && not (Full_mtracking.is_set ()) then
      feedback
        "Due to the large number of function pointers in concurrent@ \
         code, the memory tracking dataflow analysis is deactivated@ \
         when activating the concurrency support of E-ACSL.";
    Full_mtracking.on ();
    if Temporal_validity.get () then
      abort
        "The temporal analysis in valid annotations is incompatible@ \
         with the concurrency support of E-ACSL.@ \
         Please use '-e-acsl-no-temporal-validity' or '-e-acsl-no-concurrency'@ \
         to deactivate one or the other.";
    if rtl then
      Kernel.CppExtraArgs.add "-DE_ACSL_CONCURRENCY_PTHREAD"
  end;
  (* Additionnal kernel options while parsing the RTL project. *)
  if rtl then begin
    Kernel.Keep_unused_specified_functions.off ();
    Kernel.CppExtraArgs.add
      (Format.asprintf " -DE_ACSL_MACHDEP=%s" (Kernel.Machdep.get ()));
  end

(*
Local Variables:
compile-command: "make -C ../../../.."
End:
*)
