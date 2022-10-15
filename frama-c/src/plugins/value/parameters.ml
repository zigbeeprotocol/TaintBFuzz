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

open Self

(* Dependencies to kernel options *)
let kernel_parameters_correctness = [
  Kernel.MainFunction.parameter;
  Kernel.LibEntry.parameter;
  Kernel.AbsoluteValidRange.parameter;
  Kernel.InitializedPaddingLocals.parameter;
  Kernel.SafeArrays.parameter;
  Kernel.UnspecifiedAccess.parameter;
  Kernel.SignedOverflow.parameter;
  Kernel.UnsignedOverflow.parameter;
  Kernel.LeftShiftNegative.parameter;
  Kernel.RightShiftNegative.parameter;
  Kernel.SignedDowncast.parameter;
  Kernel.UnsignedDowncast.parameter;
  Kernel.PointerDowncast.parameter;
  Kernel.SpecialFloat.parameter;
  Kernel.InvalidBool.parameter;
  Kernel.InvalidPointer.parameter;
]

let parameters_correctness = ref Typed_parameter.Set.empty
let parameters_tuning = ref Typed_parameter.Set.empty
let add_dep p =
  let state = State.get p.Typed_parameter.name in
  State_builder.Proxy.extend [state] Self.proxy
let add_correctness_dep p =
  if Typed_parameter.Set.mem p !parameters_correctness then
    Kernel.abort "adding correctness parameter %a twice"
      Typed_parameter.pretty p;
  add_dep p;
  parameters_correctness := Typed_parameter.Set.add p !parameters_correctness
let add_precision_dep p =
  if Typed_parameter.Set.mem p !parameters_tuning then
    Kernel.abort "adding tuning parameter %a twice"
      Typed_parameter.pretty p;
  add_dep p;
  parameters_tuning := Typed_parameter.Set.add p !parameters_tuning

let () = List.iter add_correctness_dep kernel_parameters_correctness

module ForceValues =
  WithOutput
    (struct
      let option_name = "-eva"
      let help = "Compute values"
      let output_by_default = true
    end)
let () = ForceValues.add_aliases ~deprecated:true ["-val"]

let domains = add_group "Abstract Domains"
let precision_tuning = add_group "Precision vs. time"
let initial_context = add_group "Initial Context"
let performance = add_group "Results memoization vs. time"
let interpreter = add_group "Deterministic programs"
let alarms = add_group "Propagation and alarms "
let malloc = add_group "Dynamic allocation"

(* -------------------------------------------------------------------------- *)
(* --- Eva domains                                                        --- *)
(* -------------------------------------------------------------------------- *)

let () = Parameter_customize.set_group domains
module Domains =
  Filled_string_set
    (struct
      let option_name = "-eva-domains"
      let arg_name = "d1,...,dn"
      let help = "Enable a list of analysis domains."
      let default = Datatype.String.Set.of_list ["cvalue"]
    end)
let () = add_precision_dep Domains.parameter

let remove_domain name =
  Domains.set (Datatype.String.Set.filter ((!=) name) (Domains.get ()))

(* For backward compatibility, creates an invisible option for the domain [name]
   that sets up -eva-domains with [name]. To be removed one day. *)
let create_domain_option name =
  let option_name =
    match name with
    | "apron-box" -> "-eva-apron-box"
    | "apron-octagon" -> "-eva-apron-oct"
    | "apron-polka-loose" -> "-eva-polka-loose"
    | "apron-polka-strict" -> "-eva-polka-strict"
    | "apron-polka-equality" -> "-eva-polka-equalities"
    | _ -> "-eva-" ^ name ^ "-domain"
  in
  let module Input = struct
    let option_name = option_name
    let help = "Use the " ^ name ^ " domain of eva."
    let default = name = "cvalue"
  end in
  Parameter_customize.set_group domains;
  Parameter_customize.is_invisible ();
  let module Parameter = Bool (Input) in
  Parameter.add_set_hook
    (fun _old _new ->
       warning "Option %s is deprecated. Use -eva-domains %s%s instead."
         option_name (if _new then "" else "-") name;
       if _new then Domains.add name else remove_domain name)

let () = Parameter_customize.set_group performance
module NoResultsDomains =
  String_set
    (struct
      let option_name = "-eva-no-results-domain"
      let arg_name = "domains"
      let help = "Do not record the states of some domains during the analysis."
    end)
let () = add_dep NoResultsDomains.parameter

(* List (name, descr) of available domains. *)
let domains_ref = ref []

(* Help message for the -eva-domains option, with the list of currently
   available domains. *)
let domains_help () =
  let pp_str_list = Pretty_utils.pp_list ~sep:", " Format.pp_print_string in
  Format.asprintf
    "Enable a list of analysis domains. Available domains are: %a. \
     Use -eva-domains help to print a short description of each domain."
    pp_str_list (List.rev_map fst !domains_ref)

(* Prints the list of available domains with their description. *)
let domains_list () =
  let pp_dom fmt (name, descr) =
    Format.fprintf fmt "%-20s @[%t@]" name
      (fun fmt -> Format.pp_print_text fmt descr)
  in
  feedback ~level:0
    "List of available domains:@,%a"
    (Pretty_utils.pp_list ~pre:"@[<v>" ~sep:"@," ~suf:"@]" pp_dom)
    (List.rev !domains_ref);
  raise Cmdline.Exit

(* Registers a new domain. Updates the help message of -eva-domains. *)
let register_domain ~name ~descr =
  create_domain_option name;
  domains_ref := (name, descr) :: !domains_ref;
  Cmdline.replace_option_help
    Domains.option_name ~plugin:"eva" ~group:domains (domains_help ())

(* Checks that a domain has been registered. *)
let check_domain option_name domain =
  if domain = "help" || domain = "list"
  then domains_list ()
  else if not (List.exists (fun (name, _) -> name = domain) !domains_ref)
  then
    let pp_str_list = Pretty_utils.pp_list ~sep:",@ " Format.pp_print_string in
    abort "invalid domain %S for option %s.@.Possible domains are: %a"
      domain option_name pp_str_list (List.rev_map fst !domains_ref)

let () =
  let hook option_name = fun _old domains ->
    Datatype.String.Set.iter (check_domain option_name) domains
  in
  Domains.add_set_hook (hook Domains.name);
  NoResultsDomains.add_set_hook (hook NoResultsDomains.name)

let () = Parameter_customize.set_group domains
module DomainsFunction =
  Make_multiple_map
    (struct
      include Datatype.String
      let of_string str = check_domain "-eva-domains-function" str; str
      let of_singleton_string = no_element_of_string
      let to_string str = str
    end)
    (struct
      include Domain_mode.Function_Mode
      let of_string ~key ~prev str =
        try of_string ~key ~prev str
        with Invalid_argument msg -> raise (Cannot_build msg)
    end)
    (struct
      let option_name = "-eva-domains-function"
      let help = "Enable a domain only for the given functions. \
                  <d:f+> enables the domain [d] from function [f] \
                  (the domain is enabled in all functions called from [f]). \
                  <d:f-> disables the domain [d] from function [f]."
      let arg_name = "d:f"
      let default = Datatype.String.Map.empty
      let dependencies = []
    end)
let () = add_precision_dep DomainsFunction.parameter

let enabled_domains () =
  let domains = Domains.get () in
  let domains_by_fct = DomainsFunction.get () in
  List.filter
    (fun (name, _) -> Datatype.String.Set.mem name domains
                      || Datatype.String.Map.mem name domains_by_fct)
    !domains_ref

let () = Parameter_customize.set_group domains
module EqualityCall =
  String
    (struct
      let option_name = "-eva-equality-through-calls"
      let help = "Propagate equalities through function calls (from the caller \
                  to the called function): none, only equalities between formal \
                  parameters and concrete arguments, or all. "
      let default = "formals"
      let arg_name = "none|formals|all"
    end)
let () = EqualityCall.set_possible_values ["none"; "formals"; "all"]
let () = add_precision_dep EqualityCall.parameter

let () = Parameter_customize.set_group domains
module EqualityCallFunction =
  Kernel_function_map
    (struct
      include Datatype.String
      type key = Cil_types.kernel_function
      let of_string ~key:_ ~prev:_ = function
        | None | Some ("none" | "formals" | "all") as x -> x
        | _ -> raise (Cannot_build "must be 'none', 'formals' or 'all'.")
      let to_string ~key:_ s = s
    end)
    (struct
      let option_name = "-eva-equality-through-calls-function"
      let help = "Propagate equalities through calls to specific functions. \
                  Overrides -eva-equality-call."
      let default = Kernel_function.Map.empty
      let arg_name = "f:none|formals|all"
    end)
let () = add_precision_dep EqualityCallFunction.parameter

let () = Parameter_customize.set_group domains
module OctagonCall =
  Bool
    (struct
      let option_name = "-eva-octagon-through-calls"
      let help = "Propagate relations inferred by the octagon domain \
                  through function calls. Disabled by default: \
                  the octagon analysis is intra-procedural, starting \
                  each function with an empty octagon state, \
                  and losing the octagons inferred at the end. \
                  The interprocedural analysis is more precise but slower."
      let default = false
    end)
let () = add_precision_dep OctagonCall.parameter

let () = Parameter_customize.set_group domains
module Numerors_Real_Size =
  Int
    (struct
      let default = 128
      let option_name = "-eva-numerors-real-size"
      let arg_name = "n"
      let help =
        "Set <n> as the significand size of the MPFR representation \
         of reals used by the numerors domain (defaults to 128)"
    end)
let () = Numerors_Real_Size.set_range ~min:1 ~max:max_int
let () = add_precision_dep Numerors_Real_Size.parameter

let () = Parameter_customize.set_group domains
module Numerors_Mode =
  String
    (struct
      let option_name = "-eva-numerors-interaction"
      let help = "Define how the numerors domain infers the absolute and the \
                  relative errors:\n\
                  - relative: the relative is deduced from the absolute;\n\
                  - absolute: the absolute is deduced from the relative;\n\
                  - none: absolute and relative are computed separately;\n\
                  - both: reduced product between absolute and relative."
      let default = "both"
      let arg_name = "relative|absolute|none|both"
    end)
let () =
  Numerors_Mode.set_possible_values ["relative"; "absolute"; "none"; "both"]
let () = add_precision_dep Numerors_Mode.parameter

let () = Parameter_customize.set_group domains
module TracesUnrollLoop =
  Bool
    (struct
      let option_name = "-eva-traces-unroll-loop"
      let help = "Specify if the traces domain should unroll the loops."
      let default = true
    end)
let () = add_precision_dep TracesUnrollLoop.parameter

let () = Parameter_customize.set_group domains
module TracesUnifyLoop =
  Bool
    (struct
      let option_name = "-eva-traces-unify-loop"
      let help = "Specify if all the instances of a loop should try \
                  to share theirs traces."
      let default = false
    end)
let () = add_precision_dep TracesUnifyLoop.parameter

let () = Parameter_customize.set_group domains
module TracesDot = Filepath
    (struct
      let option_name = "-eva-traces-dot"
      let arg_name = "FILENAME"
      let file_kind = "DOT"
      let existence = Fc_Filepath.Indifferent
      let help = "Output to the given filename the Cfg in dot format."
    end)

let () = Parameter_customize.set_group domains
module TracesProject = Bool
    (struct
      let option_name = "-eva-traces-project"
      let help = "Try to convert the Cfg into a program in a new project."
      let default = false
    end)

let () = Parameter_customize.set_group domains
module MultidimSegmentLimit = Int
    (struct
      let option_name = "-eva-multidim-segment-limit"
      let arg_name = "N"
      let help = "Limit the number of segments in the abstraction of arrays."
      let default = 8
    end)
let () = MultidimSegmentLimit.set_range ~min:3 ~max:max_int
let () = add_precision_dep MultidimSegmentLimit.parameter

let () = Parameter_customize.set_group domains
module MultidimDisjunctiveInvariants = False
    (struct
      let option_name = "-eva-multidim-disjunctive-invariants"
      let help = "Try to infer structures disjunctive invariants."
    end)
let () = add_precision_dep MultidimDisjunctiveInvariants.parameter


(* -------------------------------------------------------------------------- *)
(* --- Performance options                                                --- *)
(* -------------------------------------------------------------------------- *)

let () = Parameter_customize.set_group performance
module NoResultsFunctions =
  Fundec_set
    (struct
      let option_name = "-eva-no-results-function"
      let arg_name = "f"
      let help = "Do not record the values obtained for the statements of \
                  function f"
    end)
let () = add_dep NoResultsFunctions.parameter

let () = Parameter_customize.set_group performance
module ResultsAll =
  True
    (struct
      let option_name = "-eva-results"
      let help = "Record values for each of the statements of the program."
    end)
let () = add_dep ResultsAll.parameter

let () = Parameter_customize.set_group performance
module JoinResults =
  Bool
    (struct
      let option_name = "-eva-join-results"
      let help = "Precompute consolidated states once Eva is computed"
      let default = true
    end)

(* ------------------------------------------------------------------------- *)
(* --- Non-standard alarms                                               --- *)
(* ------------------------------------------------------------------------- *)

let () = Parameter_customize.set_group alarms
module UndefinedPointerComparisonPropagateAll =
  False
    (struct
      let option_name = "-eva-undefined-pointer-comparison-propagate-all"
      let help = "If the target program appears to contain undefined pointer \
                  comparisons, propagate both outcomes {0; 1} in addition to \
                  the emission of an alarm"
    end)
let () = add_correctness_dep UndefinedPointerComparisonPropagateAll.parameter

let () = Parameter_customize.set_group alarms
module WarnPointerComparison =
  String
    (struct
      let option_name = "-eva-warn-undefined-pointer-comparison"
      let help = "Warn on all pointer comparisons, on comparisons where \
                  the arguments have pointer type (default), or never warn"
      let default = "pointer"
      let arg_name = "all|pointer|none"
    end)
let () = WarnPointerComparison.set_possible_values ["all"; "pointer"; "none"]
let () = add_correctness_dep WarnPointerComparison.parameter

let () = Parameter_customize.set_group alarms
module WarnSignedConvertedDowncast =
  False
    (struct
      let option_name = "-eva-warn-signed-converted-downcast"
      let help = "Signed downcasts are decomposed into two operations: \
                  a conversion to the signed type of the original width, \
                  then a downcast. Warn when the downcast may exceed the \
                  destination range."
    end)
let () = add_correctness_dep WarnSignedConvertedDowncast.parameter


let () = Parameter_customize.set_group alarms
module WarnPointerSubstraction =
  True
    (struct
      let option_name = "-eva-warn-pointer-subtraction"
      let help =
        "Warn when subtracting two pointers that may not be in the same \
         allocated block, and return the pointwise difference between the \
         offsets. When unset, do not warn but generate imprecise offsets."
    end)
let () = add_correctness_dep WarnPointerSubstraction.parameter

let () = Parameter_customize.set_group alarms
let () = Parameter_customize.is_invisible ()
module IgnoreRecursiveCalls =
  False
    (struct
      let option_name = "-eva-ignore-recursive-calls"
      let help = "Deprecated."
    end)
let () =
  IgnoreRecursiveCalls.add_set_hook
    (fun _old _new ->
       warning
         "@[Option -eva-ignore-recursive-calls has no effect.@ Recursive calls \
          can be unrolled@ through option -eva-unroll-recursive-calls,@ or their \
          specification is used@ to interpret them.@]")

let () = Parameter_customize.set_group alarms
let () = Parameter_customize.argument_may_be_fundecl ();
module WarnCopyIndeterminate =
  Kernel_function_set
    (struct
      let option_name = "-eva-warn-copy-indeterminate"
      let arg_name = "f | @all"
      let help =
        "Warn when a statement copies a value that may be indeterminate \
         (uninitialized, containing an escaping address, or infinite/NaN \
         floating-point value). \
         Set by default; can be deactivated for function 'f' by '=-f', \
         or for all functions by '=-@all'."
    end)
let () = add_correctness_dep WarnCopyIndeterminate.parameter
let () = WarnCopyIndeterminate.Category.(set_default (all ()))

let () = Parameter_customize.set_group alarms
module ReduceOnLogicAlarms =
  False
    (struct
      let option_name = "-eva-reduce-on-logic-alarms"
      let help = "Force reductions by a predicate to ignore logic alarms \
                  emitted while the predicate is evaluated (experimental)"
    end)
let () = add_correctness_dep ReduceOnLogicAlarms.parameter

let () = Parameter_customize.set_group alarms
module InitializedLocals =
  False
    (struct
      let option_name = "-eva-initialized-locals"
      let help = "Local variables enter in scope fully initialized. \
                  Only useful for the analysis of programs buggy w.r.t. \
                  initialization."
    end)
let () = add_correctness_dep InitializedLocals.parameter

(* ------------------------------------------------------------------------- *)
(* --- Initial context                                                   --- *)
(* ------------------------------------------------------------------------- *)

let () = Parameter_customize.set_group initial_context
module AutomaticContextMaxDepth =
  Int
    (struct
      let option_name = "-eva-context-depth"
      let default = 2
      let arg_name = "n"
      let help = "Use <n> as the depth of the default context for Eva. \
                  (defaults to 2)"
    end)
let () = AutomaticContextMaxDepth.set_range ~min:0 ~max:max_int
let () = add_correctness_dep AutomaticContextMaxDepth.parameter

let () = Parameter_customize.set_group initial_context
module AutomaticContextMaxWidth =
  Int
    (struct
      let option_name = "-eva-context-width"
      let default = 2
      let arg_name = "n"
      let help = "Use <n> as the width of the default context for Eva. \
                  (defaults to 2)"
    end)
let () = AutomaticContextMaxWidth.set_range ~min:1 ~max:max_int
let () = add_correctness_dep AutomaticContextMaxWidth.parameter

let () = Parameter_customize.set_group initial_context
module AllocatedContextValid =
  False
    (struct
      let option_name = "-eva-context-valid-pointers"
      let help = "Only allocate valid pointers until context-depth, \
                  and then use NULL (defaults to false)"
    end)
let () = add_correctness_dep AllocatedContextValid.parameter

let () = Parameter_customize.set_group initial_context
module InitializationPaddingGlobals =
  String
    (struct
      let default = "yes"
      let option_name = "-eva-initialization-padding-globals"
      let arg_name = "yes|no|maybe"
      let help = "Specify how padding bits are initialized inside global \
                  variables. Possible values are <yes> (padding is fully \
                  initialized), <no> (padding is completely uninitialized), or \
                  <maybe> (padding may be uninitialized). Default is <yes>."
    end)
let () = InitializationPaddingGlobals.set_possible_values ["yes"; "no"; "maybe"]
let () = add_correctness_dep InitializationPaddingGlobals.parameter

(* ------------------------------------------------------------------------- *)
(* --- Tuning                                                            --- *)
(* ------------------------------------------------------------------------- *)

(* --- Iteration strategy --- *)

let () = Parameter_customize.set_group precision_tuning
let () = Parameter_customize.is_invisible ()
module DescendingIteration =
  String
    (struct
      let default = "no"
      let option_name = "-eva-descending-iteration"
      let arg_name = "no|exits|full"
      let help = "Experimental. After hitting a postfix point, try to improve \
                  the precision with either a <full> iteration or an iteration \
                  from loop head to exit paths (<exits>) or do not try anything \
                  (<no>). Default is <no>."
    end)
let () = DescendingIteration.set_possible_values ["no" ; "exits" ; "full"]
let () = add_precision_dep DescendingIteration.parameter

let () = Parameter_customize.set_group precision_tuning
let () = Parameter_customize.is_invisible ()
module HierarchicalConvergence =
  False
    (struct
      let option_name = "-eva-hierarchical-convergence"
      let help = "Experimental and unsound. Separate the convergence process \
                  of each level of nested loops. This implies that the \
                  convergence of inner loops will be completely recomputed when \
                  doing another iteration of the outer loops."
    end)
let () = add_precision_dep HierarchicalConvergence.parameter

let () = Parameter_customize.set_group precision_tuning
module WideningDelay =
  Int
    (struct
      let default = 3
      let option_name = "-eva-widening-delay"
      let arg_name = "n"
      let help =
        "Do not widen before the <n>-th iteration (defaults to 3)"
    end)
let () = WideningDelay.set_range ~min:1 ~max:max_int
let () = add_precision_dep WideningDelay.parameter

let () = Parameter_customize.set_group precision_tuning
module WideningPeriod =
  Int
    (struct
      let default = 2
      let option_name = "-eva-widening-period"
      let arg_name = "n"
      let help =
        "After the first widening, widen each <n> iterations (defaults to 2)"
    end)
let () = WideningPeriod.set_range ~min:1 ~max:max_int
let () = add_precision_dep WideningPeriod.parameter

let () = Parameter_customize.set_group precision_tuning
module RecursiveUnroll =
  Int
    (struct
      let default = 0
      let option_name = "-eva-unroll-recursive-calls"
      let arg_name = "n"
      let help = "Unroll <n> recursive calls before using the specification of \
                  the recursive function to interpret the calls."
    end)
let () = RecursiveUnroll.set_range ~min:0 ~max:max_int
let () = add_precision_dep RecursiveUnroll.parameter

(* --- Partitioning --- *)

let () = Parameter_customize.set_group precision_tuning
module SemanticUnrollingLevel =
  Zero
    (struct
      let option_name = "-eva-slevel"
      let arg_name = "n"
      let help =
        "Superpose up to <n> states when unrolling control flow. \
         The larger n, the more precise and expensive the analysis \
         (defaults to 0)"
    end)
let () = SemanticUnrollingLevel.set_range ~min:0 ~max:max_int
let () = add_precision_dep SemanticUnrollingLevel.parameter

let () = Parameter_customize.set_group precision_tuning
let () = Parameter_customize.argument_may_be_fundecl ()
module SlevelFunction =
  Kernel_function_map
    (struct
      include Datatype.Int
      type key = Cil_types.kernel_function
      let of_string ~key:_ ~prev:_ s =
        Option.map
          (fun s ->
             try int_of_string s
             with Failure _ ->
               raise (Cannot_build ("'" ^ s ^ "' is not an integer")))
          s
      let to_string ~key:_ = Option.map string_of_int
    end)
    (struct
      let option_name = "-eva-slevel-function"
      let arg_name = "f:n"
      let help = "Override slevel with <n> when analyzing <f>"
      let default = Kernel_function.Map.empty
    end)
let () = add_precision_dep SlevelFunction.parameter

let () = Parameter_customize.set_group precision_tuning
module SlevelMergeAfterLoop =
  Kernel_function_set
    (struct
      let option_name = "-eva-slevel-merge-after-loop"
      let arg_name = "f | @all"
      let help =
        "When set, the different execution paths that originate from the body \
         of a loop are merged before entering the next execution."
    end)
let () = add_precision_dep SlevelMergeAfterLoop.parameter

let () = Parameter_customize.set_group precision_tuning
module MinLoopUnroll =
  Int
    (struct
      let option_name = "-eva-min-loop-unroll"
      let arg_name = "n"
      let default = 0
      let help =
        "Unroll <n> loop iterations for each loop, regardless of the slevel \
         settings and the number of states already propagated. \
         Can be overwritten on a case-by-case basis by loop unroll annotations."
    end)
let () = add_precision_dep MinLoopUnroll.parameter
let () = MinLoopUnroll.set_range ~min:0 ~max:max_int

let () = Parameter_customize.set_group precision_tuning
module AutoLoopUnroll =
  Int
    (struct
      let option_name = "-eva-auto-loop-unroll"
      let arg_name = "n"
      let default = 0
      let help = "Limit of the automatic loop unrolling: all loops whose \
                  number of iterations can be easily bounded by <n> \
                  are completely unrolled."
    end)
let () = add_precision_dep AutoLoopUnroll.parameter
let () = AutoLoopUnroll.set_range ~min:0 ~max:max_int

let () = Parameter_customize.set_group precision_tuning
module DefaultLoopUnroll =
  Int
    (struct
      let option_name = "-eva-default-loop-unroll"
      let arg_name = "n"
      let default = 100
      let help =
        "Define the default limit for loop unroll annotations that do \
         not explicitly provide a limit."
    end)
let () = add_precision_dep DefaultLoopUnroll.parameter
let () = DefaultLoopUnroll.set_range ~min:0 ~max:max_int

let () = Parameter_customize.set_group precision_tuning
module HistoryPartitioning =
  Int
    (struct
      let option_name = "-eva-partition-history"
      let arg_name = "n"
      let default = 0
      let help =
        "Keep states distinct as long as the <n> last branching in their \
         traces are also distinct. (A value of 0 deactivates this feature)"
    end)
let () = add_precision_dep HistoryPartitioning.parameter
let () = HistoryPartitioning.set_range ~min:0 ~max:max_int

let () = Parameter_customize.set_group precision_tuning
module ValuePartitioning =
  String_set
    (struct
      let option_name = "-eva-partition-value"
      let help = "Partition the space of reachable states according to the \
                  possible values of the global(s) variable(s) V."
      let arg_name = "V"
    end)
let () = add_precision_dep ValuePartitioning.parameter

let use_global_value_partitioning vi =
  ValuePartitioning.add vi.Cil_types.vname

let () = Parameter_customize.set_group precision_tuning
module SplitLimit =
  Int
    (struct
      let option_name = "-eva-split-limit"
      let arg_name = "N"
      let default = 100
      let help = "Prevent split annotations or -eva-partition-value from \
                  enumerating more than N cases"
    end)
let () = add_precision_dep SplitLimit.parameter
let () = SplitLimit.set_range ~min:0 ~max:max_int

let () = Parameter_customize.set_group precision_tuning
module InterproceduralSplits =
  False
    (struct
      let option_name = "-eva-interprocedural-splits"
      let help = "Keep partitioning splits through function returns"
    end)
let () = add_precision_dep InterproceduralSplits.parameter

let () = Parameter_customize.set_group precision_tuning
module InterproceduralHistory =
  False
    (struct
      let option_name = "-eva-interprocedural-history"
      let help = "Keep partitioning history through function returns"
    end)
let () = add_precision_dep InterproceduralHistory.parameter

let () = Parameter_customize.set_group precision_tuning
let () = Parameter_customize.argument_may_be_fundecl ()
module SplitReturnFunction =
  Kernel_function_map
    (struct
      (* this type is ad-hoc: cannot use Kernel_function_multiple_map here *)
      include Split_strategy
      type key = Cil_types.kernel_function
      let of_string ~key:_ ~prev:_ s =
        try Option.map Split_strategy.of_string s
        with Split_strategy.ParseFailure s ->
          raise (Cannot_build ("unknown split strategy " ^ s))
      let to_string ~key:_ v =
        Option.map Split_strategy.to_string v
    end)
    (struct
      let option_name = "-eva-split-return-function"
      let arg_name = "f:n"
      let help = "Split return states of function <f> according to \
                  \\result == n and \\result != n"
      let default = Kernel_function.Map.empty
    end)
let () = add_precision_dep SplitReturnFunction.parameter

let () = Parameter_customize.set_group precision_tuning
module SplitReturn =
  String
    (struct
      let option_name = "-eva-split-return"
      let arg_name = "mode"
      let default = ""
      let help = "When 'mode' is a number, or 'full', this is equivalent \
                  to -eva-split-return-function f:mode for all functions f. \
                  When mode is 'auto', automatically split states at the end \
                  of all functions, according to the function return code"
    end)
module SplitGlobalStrategy = State_builder.Ref (Split_strategy)
    (struct
      let default () = Split_strategy.NoSplit
      let name = "Parameters.SplitGlobalStrategy"
      let dependencies = [SplitReturn.self]
    end)
let () =
  SplitReturn.add_set_hook
    (fun _ x -> SplitGlobalStrategy.set
        (try Split_strategy.of_string x
         with Split_strategy.ParseFailure s ->
           abort "@[@[incorrect argument for option %s@ (%s).@]"
             SplitReturn.name s))
let () = add_precision_dep SplitReturn.parameter

(* --- Misc --- *)

let () = Parameter_customize.set_group precision_tuning
module ILevel =
  Int
    (struct
      let option_name = "-eva-ilevel"
      let default = 8 (* Must be synchronized with Int_set.small_cardinal. *)
      let arg_name = "n"
      let help =
        "Sets of integers are represented as sets up to <n> elements. \
         Above, intervals with congruence information are used \
         (defaults to 8, must be above 2)"
    end)
let () = add_precision_dep ILevel.parameter
let () = ILevel.add_update_hook (fun _ i -> Int_set.set_small_cardinal i)
let () = ILevel.set_range ~min:2 ~max:max_int

let builtins = ref Datatype.String.Set.empty
let register_builtin name = builtins := Datatype.String.Set.add name !builtins
let mem_builtin name = Datatype.String.Set.mem name !builtins

let () = Parameter_customize.set_group precision_tuning
let () = Parameter_customize.argument_may_be_fundecl ()
module BuiltinsOverrides =
  Kernel_function_map
    (struct
      include Datatype.String
      type key = Cil_types.kernel_function
      let of_string ~key:kf ~prev:_ nameopt =
        begin match nameopt with
          | Some name ->
            if not (mem_builtin name) then
              abort "option '-eva-builtin %a:%s': undeclared builtin '%s'@.\
                     declared builtins: @[%a@]"
                Kernel_function.pretty kf name name
                (Pretty_utils.pp_list ~sep:",@ " Format.pp_print_string)
                (Datatype.String.Set.elements !builtins)
          | _ -> abort
                   "option '-eva-builtin':@ \
                    no builtin associated to function '%a',@ use '%a:<builtin>'"
                   Kernel_function.pretty kf Kernel_function.pretty kf
        end;
        nameopt
      let to_string ~key:_ name = name
    end)
    (struct
      let option_name = "-eva-builtin"
      let arg_name = "f:ffc"
      let help = "When analyzing function <f>, try to use Frama-C builtin \
                  <ffc> instead. \
                  Fall back to <f> if <ffc> cannot handle its arguments."
      let default = Kernel_function.Map.empty
    end)
let () = add_correctness_dep BuiltinsOverrides.parameter

(* Exported in Eva.mli. *)
let use_builtin key name =
  if mem_builtin name
  then BuiltinsOverrides.add (key, Some name)
  else raise Not_found

let () = Parameter_customize.set_group precision_tuning
module BuiltinsAuto =
  True
    (struct
      let option_name = "-eva-builtins-auto"
      let help = "When set, builtins will be used automatically to replace \
                  known C functions"
    end)
let () = add_correctness_dep BuiltinsAuto.parameter

let () = Parameter_customize.set_group precision_tuning
let () = Parameter_customize.set_negative_option_name ""
module BuiltinsList =
  False
    (struct
      let option_name = "-eva-builtins-list"
      let help = "List existing builtins, and which functions they \
                  are automatically associated to (if any)"
    end)

let () = Parameter_customize.set_group precision_tuning
module LinearLevel =
  Zero
    (struct
      let option_name = "-eva-subdivide-non-linear"
      let arg_name = "n"
      let help =
        "Improve precision when evaluating expressions in which a variable \
         appears multiple times, by splitting its value at most n times. \
         Defaults to 0."
    end)
let () = LinearLevel.set_range ~min:0 ~max:max_int
let () = add_precision_dep LinearLevel.parameter

let () = Parameter_customize.set_group precision_tuning
module LinearLevelFunction =
  Kernel_function_map
    (struct
      include Datatype.Int
      type key = Cil_types.kernel_function
      let of_string ~key:_ ~prev:_ s =
        Option.map
          (fun s ->
             try int_of_string s
             with Failure _ ->
               raise (Cannot_build ("'" ^ s ^ "' is not an integer")))
          s
      let to_string ~key:_ = Option.map string_of_int
    end)
    (struct
      let option_name = "-eva-subdivide-non-linear-function"
      let arg_name = "f:n"
      let help = "Override the global option -eva-subdivide-non-linear with <n>\
                  when analyzing the function <f>."
      let default = Kernel_function.Map.empty
    end)
let () = add_precision_dep LinearLevelFunction.parameter

let () = Parameter_customize.set_group precision_tuning
let () = Parameter_customize.argument_may_be_fundecl ()
module UsePrototype =
  Kernel_function_set
    (struct
      let option_name = "-eva-use-spec"
      let arg_name = "f1,..,fn"
      let help = "Use the ACSL specification of the functions instead of \
                  their definitions"
    end)
let () = add_correctness_dep UsePrototype.parameter

let () = Parameter_customize.set_group precision_tuning
module SkipLibcSpecs =
  True
    (struct
      let option_name = "-eva-skip-stdlib-specs"
      let help = "Skip ACSL specifications on functions originating from the \
                  standard library of Frama-C, when their bodies are evaluated"
    end)
let () = add_precision_dep SkipLibcSpecs.parameter


let () = Parameter_customize.set_group precision_tuning
module RmAssert =
  True
    (struct
      let option_name = "-eva-remove-redundant-alarms"
      let help = "After the analysis, try to remove redundant alarms, \
                  so that the user needs to inspect fewer of them"
    end)
let () = add_precision_dep RmAssert.parameter

let () = Parameter_customize.set_group precision_tuning
module MemExecAll =
  True
    (struct
      let option_name = "-eva-memexec"
      let help = "Speed up analysis by not recomputing functions already \
                  analyzed in the same context. \
                  Callstacks for which the analysis has not been recomputed \
                  are incorrectly shown as dead in the GUI."
    end)

let () = Parameter_customize.set_group precision_tuning
module ArrayPrecisionLevel =
  Int
    (struct
      let default = 200
      let option_name = "-eva-plevel"
      let arg_name = "n"
      let help = "Use <n> as the precision level for arrays accesses. \
                  Array accesses are precise as long as the interval for the \
                  index contains less than n values. (defaults to 200)"
    end)
let () = ArrayPrecisionLevel.set_range ~min:0 ~max:max_int
let () = add_precision_dep ArrayPrecisionLevel.parameter
let () = ArrayPrecisionLevel.add_update_hook
    (fun _ v -> Offsetmap.set_plevel v)

(* ------------------------------------------------------------------------- *)
(* --- Messages                                                          --- *)
(* ------------------------------------------------------------------------- *)

let () = Parameter_customize.set_group messages
module ValShowProgress =
  False
    (struct
      let option_name = "-eva-show-progress"
      let help = "Show progression messages during analysis"
    end)

let () = Parameter_customize.set_group messages
module ValShowPerf =
  False
    (struct
      let option_name = "-eva-show-perf"
      let help = "Compute and show a summary of the time spent analyzing \
                  function calls"
    end)

let () = Parameter_customize.set_group messages
module ValPerfFlamegraphs =
  Filepath
    (struct
      let option_name = "-eva-flamegraph"
      let arg_name = "file"
      let file_kind = "Text for flamegraph"
      let existence = Fc_Filepath.Indifferent
      let help = "Dump a summary of the time spent analyzing function calls \
                  in a format suitable for the Flamegraph tool \
                  (http://www.brendangregg.com/flamegraphs.html)"
    end)


let () = Parameter_customize.set_group messages
module ShowSlevel =
  Int
    (struct
      let option_name = "-eva-show-slevel"
      let default = 100
      let arg_name = "n"
      let help = "Period for showing consumption of the allotted slevel during \
                  analysis"
    end)
let () = ShowSlevel.set_range ~min:1 ~max:max_int

let () = Parameter_customize.set_group messages
module PrintCallstacks =
  False
    (struct
      let option_name = "-eva-print-callstacks"
      let help = "When printing a message, also show the current call stack"
    end)

let () = Parameter_customize.set_group messages
module ReportRedStatuses =
  Filepath
    (struct
      let option_name = "-eva-report-red-statuses"
      let arg_name = "filename"
      let file_kind = "CSV"
      let existence = Fc_Filepath.Indifferent
      let help = "Output the list of \"red properties\" in a csv file of the \
                  given name. These are the properties which were invalid for \
                  some states. Their consolidated status may not be invalid, \
                  but they should often be investigated first."
    end)

let () = Parameter_customize.set_group messages
module NumerorsLogFile =
  Filepath
    (struct
      let option_name = "-eva-numerors-log-file"
      let arg_name = "file"
      let file_kind = "Text"
      let existence = Fc_Filepath.Indifferent
      let help = "The Numerors domain will save each call to the DPRINT \
                  function in the given file"
    end)

(* ------------------------------------------------------------------------- *)
(* --- Interpreter mode                                                  --- *)
(* ------------------------------------------------------------------------- *)

let () = Parameter_customize.set_group interpreter
module InterpreterMode =
  False
    (struct
      let option_name = "-eva-interpreter-mode"
      let help = "Stop at first call to a library function, if main() has \
                  arguments, on undecided branches"
    end)

let () = Parameter_customize.set_group interpreter
module StopAtNthAlarm =
  Int(struct
    let option_name = "-eva-stop-at-nth-alarm"
    let default = max_int
    let arg_name = "n"
    let help = "Abort the analysis when the nth alarm is emitted."
  end)
let () = StopAtNthAlarm.set_range ~min:0 ~max:max_int

(* -------------------------------------------------------------------------- *)
(* --- Ugliness required for correctness                                  --- *)
(* -------------------------------------------------------------------------- *)

let () = Parameter_customize.is_invisible ()
module InitialStateChanged =
  Int (struct
    let option_name = "-eva-new-initial-state"
    let default = 0
    let arg_name = "n"
    let help = ""
  end)
(* Changing the user-supplied initial state (or the arguments of main) through
   the API of Db.Value does reset the state of Value, but *not* the property
   statuses that Value has positioned. Currently, statuses can only depend
   on a command-line parameter. We use the dummy one above to force a reset
   when needed. *)
let () =
  add_correctness_dep InitialStateChanged.parameter;
  Db.Value.initial_state_changed :=
    (fun () -> InitialStateChanged.set (InitialStateChanged.get () + 1))


(* -------------------------------------------------------------------------- *)
(* --- Eva options                                                        --- *)
(* -------------------------------------------------------------------------- *)

let () = Parameter_customize.set_group precision_tuning
module EnumerateCond =
  Bool
    (struct
      let option_name = "-eva-enumerate-cond"
      let help = "Activate reduce_by_cond_enumerate."
      let default = true
    end)
let () = add_precision_dep EnumerateCond.parameter


let () = Parameter_customize.set_group precision_tuning
module OracleDepth =
  Int
    (struct
      let option_name = "-eva-oracle-depth"
      let help = "Maximum number of successive uses of the oracle by the domain \
                  for the evaluation of an expression. Set 0 to disable the \
                  oracle."
      let default = 2
      let arg_name = ""
    end)
let () = OracleDepth.set_range ~min:0 ~max:max_int
let () = add_precision_dep OracleDepth.parameter

let () = Parameter_customize.set_group precision_tuning
module ReductionDepth =
  Int
    (struct
      let option_name = "-eva-reduction-depth"
      let help = "Maximum number of successive backward reductions that the \
                  domain may initiate."
      let default = 4
      let arg_name = ""
    end)
let () = ReductionDepth.set_range ~min:0 ~max:max_int
let () = add_precision_dep ReductionDepth.parameter


(* -------------------------------------------------------------------------- *)
(* --- Dynamic allocation                                                 --- *)
(* -------------------------------------------------------------------------- *)

let () = Parameter_customize.set_group malloc
module AllocBuiltin =
  String
    (struct
      let option_name = "-eva-alloc-builtin"
      let help = "Select the behavior of allocation builtins. \
                  By default, they use up to [-eva-mlevel] bases \
                  for each callstack (<by_stack>). They can also \
                  use one <imprecise> base for all allocations, \
                  create a <fresh> strong base at each call, \
                  or create a <fresh_weak> base at each call."
      let default = "by_stack"
      let arg_name = "imprecise|by_stack|fresh|fresh_weak"
    end)
let () = add_precision_dep AllocBuiltin.parameter
let () =
  AllocBuiltin.set_possible_values
    ["imprecise"; "by_stack"; "fresh"; "fresh_weak"]

let () = Parameter_customize.set_group malloc
module AllocFunctions =
  Filled_string_set
    (struct
      let option_name = "-eva-alloc-functions"
      let arg_name = "f1,...,fn"
      let help = "Control call site creation for dynamically allocated bases. \
                  Dynamic allocation builtins use the call sites of \
                  malloc/calloc/realloc to know \
                  where to create new bases. This detection does not work for \
                  custom allocators or wrappers on top of them, unless they \
                  are listed here. \
                  By default, contains malloc, calloc and realloc."
      let default = Datatype.String.Set.of_list ["malloc"; "calloc"; "realloc"]
    end)
let () = AllocFunctions.add_aliases ["-eva-malloc-functions"]

let () = Parameter_customize.set_group malloc
module AllocReturnsNull=
  True
    (struct
      let option_name = "-eva-alloc-returns-null"
      let help = "Memory allocation built-ins (malloc, calloc, realloc) are \
                  modeled as nondeterministically returning a null pointer"
    end)
let () = add_correctness_dep AllocReturnsNull.parameter

let () = Parameter_customize.set_group malloc
module MallocLevel =
  Int
    (struct
      let option_name = "-eva-mlevel"
      let default = 0
      let arg_name = "m"
      let help = "Set to [m] the number of precise dynamic allocations \
                  besides the initial one, for each callstack (defaults to 0)"
    end)
let () = MallocLevel.set_range ~min:0 ~max:max_int
let () = add_precision_dep MallocLevel.parameter

(* -------------------------------------------------------------------------- *)
(* --- Deprecated options and aliases                                     --- *)
(* -------------------------------------------------------------------------- *)

let () = Parameter_customize.set_group alarms
let () = Parameter_customize.is_invisible ()
module AllRoundingModesConstants =
  False
    (struct
      let option_name = "-eva-all-rounding-modes-constants"
      let help = "Deprecated. Take into account the possibility of constants \
                  not being converted to the nearest representable value, \
                  or being converted to higher precision"
    end)
let () = add_correctness_dep AllRoundingModesConstants.parameter
let () =
  AllRoundingModesConstants.add_set_hook
    (fun _old _new ->
       warning "Option -eva-all-rounding-modes-constants is now deprecated.@ \
                Please contact us if you need it.")

let deprecated_aliases : ((module Parameter_sig.S) * string) list =
  [ (module SemanticUnrollingLevel), "-slevel"
  ; (module SlevelFunction), "-slevel-function"
  ; (module NoResultsFunctions), "-no-results-function"
  ; (module ResultsAll), "-results"
  ; (module JoinResults), "-val-join-results"
  ; (module AllRoundingModesConstants), "-all-rounding-modes-constants"
  ; (module UndefinedPointerComparisonPropagateAll), "-undefined-pointer-comparison-propagate-all"
  ; (module WarnPointerComparison), "-val-warn-undefined-pointer-comparison"
  ; (module WarnSignedConvertedDowncast), "-val-warn-signed-converted-downcast"
  ; (module WarnPointerSubstraction), "-val-warn-pointer-subtraction"
  ; (module IgnoreRecursiveCalls), "-val-ignore-recursive-calls"
  ; (module WarnCopyIndeterminate), "-val-warn-copy-indeterminate"
  ; (module ReduceOnLogicAlarms), "-val-reduce-on-logic-alarms"
  ; (module InitializedLocals), "-val-initialized-locals"
  ; (module AutomaticContextMaxDepth), "-context-depth"
  ; (module AutomaticContextMaxWidth), "-context-width"
  ; (module AllocatedContextValid), "-context-valid-pointers"
  ; (module InitializationPaddingGlobals), "-val-initialization-padding-globals"
  ; (module WideningDelay), "-wlevel"
  ; (module SlevelMergeAfterLoop), "-val-slevel-merge-after-loop"
  ; (module SplitReturnFunction), "-val-split-return-function"
  ; (module SplitReturn), "-val-split-return"
  ; (module ILevel), "-val-ilevel"
  ; (module BuiltinsOverrides), "-val-builtin"
  ; (module BuiltinsAuto), "-val-builtins-auto"
  ; (module BuiltinsList), "-val-builtins-list"
  ; (module LinearLevel), "-val-subdivide-non-linear"
  ; (module UsePrototype), "-val-use-spec"
  ; (module SkipLibcSpecs), "-val-skip-stdlib-specs"
  ; (module RmAssert), "-remove-redundant-alarms"
  ; (module MemExecAll), "-memexec-all"
  ; (module ArrayPrecisionLevel), "-plevel"
  ; (module ValShowProgress), "-val-show-progress"
  ; (module ValShowPerf), "-val-show-perf"
  ; (module ValPerfFlamegraphs), "-val-flamegraph"
  ; (module ShowSlevel), "-val-show-slevel"
  ; (module PrintCallstacks), "-val-print-callstacks"
  ; (module InterpreterMode), "-val-interpreter-mode"
  ; (module StopAtNthAlarm), "-val-stop-at-nth-alarm"
  ; (module AllocFunctions), "-val-malloc-functions"
  ; (module AllocReturnsNull), "-val-alloc-returns-null"
  ; (module MallocLevel), "-val-mlevel"
  ]

let add_deprecated_alias ((module P: Parameter_sig.S), name) =
  P.add_aliases ~visible:false ~deprecated:true [name]

let () = List.iter add_deprecated_alias deprecated_aliases


(* -------------------------------------------------------------------------- *)
(* --- Meta options                                                       --- *)
(* -------------------------------------------------------------------------- *)

module Precision =
  Int
    (struct
      let option_name = "-eva-precision"
      let arg_name = "n"
      let default = -1
      let help = "Meta-option that automatically sets up some Eva parameters \
                  for a quick configuration of an analysis, \
                  from 0 (fastest but rather imprecise analysis) \
                  to 11 (accurate but potentially slow analysis)."
    end)
let () = Precision.set_range ~min:(-1) ~max:11
let () = add_precision_dep Precision.parameter

(* Sets a parameter [P] to [t], unless it has already been set by any other
   means. *)
let set (type t) (module P: Parameter_sig.S with type t = t) =
  let previous = ref (P.get ()) in
  fun ~default t ->
    let already_set = P.is_set () && not (P.equal !previous (P.get ())) in
    if not already_set then begin
      if default then P.clear () else P.set t;
      previous := P.get ();
    end;
    let str = Typed_parameter.get_value P.parameter in
    let str = match P.parameter.Typed_parameter.accessor with
      | Typed_parameter.String _ -> "\'" ^ str ^ "\'"
      | _ -> str
    in
    printf "  option %s %sset to %s%s." P.name
      (if already_set then "already " else "") str
      (if already_set && not (P.equal t (P.get ())) then " (not modified)"
       else if P.is_default () then " (default value)" else "")

(* List of configure functions to be called for -eva-precision. *)
let configures = ref []

(* Binds the parameter [P] to the function [f] that gives the parameter value
   for a precision n. *)
let bind (type t) (module P: Parameter_sig.S with type t = t) f =
  let set = set (module P) in
  configures := (fun n -> set ~default:(n < 0) (f n)) :: !configures

let domains n =
  let (<+>) domains (x, name) = if n >= x then name :: domains else domains in
  [ "cvalue" ]
  <+> (1, "symbolic-locations")
  <+> (2, "equality")
  <+> (3, "gauges")
  <+> (5, "octagon")

(*  power             0    1   2   3    4    5    6    7    8     9    10    11 *)
let slevel_power = [| 0;  10; 20; 35;  60; 100; 160; 250; 500; 1000; 2000; 5000 |]
let ilevel_power = [| 8;  12; 16; 24;  32;  48;  64; 128; 192;  256;  256;  256 |]
let plevel_power = [| 10; 20; 40; 70; 100; 150; 200; 300; 500;  700; 1000; 2000 |]
let auto_unroll =  [| 0;  16; 32; 64;  96; 128; 192; 256; 384;  512;  768; 1024 |]

let get array n = if n < 0 then 0 else array.(n)

let () =
  bind (module MinLoopUnroll) (fun n -> max 0 (n - 7));
  bind (module AutoLoopUnroll) (get auto_unroll);
  bind (module WideningDelay) (fun n -> 1 + n / 2);
  bind (module HistoryPartitioning) (fun n -> (n - 1) / 5);
  bind (module SemanticUnrollingLevel) (get slevel_power);
  bind (module ILevel) (get ilevel_power);
  bind (module ArrayPrecisionLevel) (get plevel_power);
  bind (module LinearLevel) (fun n -> n * 20);
  bind (module RmAssert) (fun n -> n > 0);
  bind (module Domains) (fun n -> Datatype.String.Set.of_list (domains n));
  bind (module SplitReturn) (fun n -> if n > 3 then "auto" else "");
  bind (module EqualityCall) (fun n -> if n > 4 then "formals" else "none");
  bind (module OctagonCall) (fun n -> n > 6);
  ()

let set_analysis n =
  feedback "Option %s %i detected, \
            automatic configuration of the analysis:" Precision.name n;
  List.iter ((|>) n) (List.rev !configures)

let configure_precision () =
  if Precision.is_set () then set_analysis (Precision.get ())

(* -------------------------------------------------------------------------- *)
(* --- Freeze parameters. MUST GO LAST                                    --- *)
(* -------------------------------------------------------------------------- *)

let parameters_correctness =
  Typed_parameter.Set.elements !parameters_correctness
let parameters_tuning =
  Typed_parameter.Set.elements !parameters_tuning
