#compdef frama-c

# -----------------------------------------------------------------------------
#                        zsh completion for Frama-C
#
# This file should be renamed _frama-c and placed in a directory listed in the
# $fpath variable. You can add a directory to $fpath by adding a line like the
# following to your ~/.zshrc file:
#   fpath=(~/newdir $fpath)
#
# To enable the same completion for frama-c-gui, also add to your ~/.zshrc file:
#   compdef frama-c-gui=frama-c
# It also works with relative paths, such as 'bin/frama-c'
#
# This completion is incomplete, and supports only some parameters of the kernel
# and of some plug-ins: Value Analysis, Metrics.
#
# -----------------------------------------------------------------------------


containsElement () {
  local e
  for e in "${@:2}"; do [[ "$e" == "$1" ]] && return 0; done
  return 1
}

_funs () {
  _message -r "A set of functions is expected";
  _values : \
    "@all[apply parameter to all functions]" \
    ""
}

# -----------------------------------------------------------------------------
#                                 Kernel
# -----------------------------------------------------------------------------

analysis_options=(
  "-main=[entry point for analysis]:function"
  "-lib-entry[run analysis for an incomplete application]"
  {,-no}"-warn-signed-overflow[generate alarms for signed operations that overflow]"
  {,-no}"-warn-unsigned-overflow[generate alarms for unsigned operations that overflow]"
  {,-no}"-warn-signed-downcast[generate alarms when signed downcasts may exceed the destination range]"
  {,-no}"-warn-unsigned-downcast[generate alarms when unsigned downcasts may exceed the destination range]"
  {,-no}"-safe-array[for multidimensional arrays or arrays that are fields inside structs, assume that accesses are in bounds]"
  "-absolute-valid-range=[valid range for absolute addresses]:min-max"
  "-load=[load a previously-saved session from file]:file:_files"
  "-save=[at exit, save the session into file]:filename"
)

_kernel_msg_key () {
  _values -s , -S : 'kernel_keys'                        \
    "\*"                                                 \
    "asm:a:(contracts)"                                  \
    "cabs2cil:c:(cast chunk createGlobal initializers)"  \
    "check" "check\:strict\:volatile"                    \
    "cmdline" "comments" "dataflows" "dominators"        \
    "dynlink" "emitter" "exn_flow"                       \
    "file" "file:f:(annotation transformation)"          \
    "filter" "globals" "mergecil" "mergecil\:getNode"    \
    "natural_loops" "parse\:rmtmps" "pp"                 \
    "printer:pp:(builtins logic-coercions logic-types sid unspecified vid)" \
    "project" "property_status" "property_status\:graph" \
    "task" "ulevel" "visitor"
}

kernel_arguments=(
  "-verbose=[general level of verbosity]:integer"
  "-debug=[general level of debug]:integer"
  "-kernel-msg-key=[enables message display for categories]:keys:_kernel_msg_key"
  "-float-normal[display floats with internal routine]"
  "-float-relative[display float intervals as \[lower_bound ++ width\]]"
  "-float-hex[display floats as hexadecimal]"
  "-big-ints-hex=[display integers larger than <n> using hexadecimal notation]:integer"
)


# -----------------------------------------------------------------------------
#                              Value Analysis
# -----------------------------------------------------------------------------

_value_msg_key () {
  _values -s , 'value keys' \
    "\*" "callbacks" "cardinal" "d-eqs" "experimental-ok" "imprecision" \
    "initial_state" "malloc" "nonlin" "restart" "strlen"
}

value_builtins=(
  "memchr:b:(Frama_C_memchr)"
  "memmove:b:(Frama_C_memcpy)"
  "memcpy:b:(Frama_C_memcpy)"
  "memset:b:(Frama_C_memset)"
  "strchr:b:(Frama_C_strchr)"
  "strlen:b:(Frama_C_strlen)" "strnlen:b:(Frama_C_strnlen)"
  "floor:b:(Frama_C_floor)" "floorf:b:(Frama_C_floorf)"
  "round:b:(Frama_C_round)" "roundf:b:(Frama_C_roundf)"
  "atan2:b:(Frama_C_atan2)"
  "cos:b:(Frama_C_cos Frama_C_cos_precise)"
  "sin:b:(Frama_C_sin Frama_C_sin_precise)"
  "mod:b:(Frama_C_fmod)"
  "log:b:(Frama_C_log)" "logf:b:(Frama_C_logf)"
  "log10:b:(Frama_C_log10)" "log10f:b:(Frama_C_log10f)"
  "pow:b:(Frama_C_pow)" "powf:b:(Frama_C_powf)"
  "sqrt:b:(Frama_C_sqrt)" "sqrtf:b:(Frama_C_sqrtf)"
  "printf:b:(Frama_C_printf)"
  "sprintf:b:(Frama_C_sprintf)" "snprintf:b:(Frama_C_snprintf)"
  "free:b:(Frama_C_free)"
  "malloc:b:(Frama_C_malloc_by_stack Frama_C_malloc_fresh Frama_C_malloc_fresh_weak)"
  "calloc:b:(Frama_C_calloc_by_stack Frama_C_calloc_fresh)"
  "realloc:b:(Frama_C_realloc Frama_C_realloc_multiple)"
)

_builtins () {
  _values -s , -S : 'builtins' ${value_builtins}
}

value_parameters=(

# value_domains
  "-no-eva-cvalue-domain[disable the default domain of eva]"
  "-eva-equality-domain[enable the equality domain of eva.]"
  "-eva-apron-oct[enable the octagon domain of apron]"
  "-eva-apron-box[enable the box domain of apron.]"
  "-eva-polka-loose[enable the loose polyhedra domain of apron]"
  "-eva-polka-strict[enable the strict polyhedra domain of apron]"
  "-eva-polka-equalities[enable the linear equalities domain of apron]"

# value_alarms
  "-val-warn-signed-converted-downcast[relaxed semantics for signed downcasts]"
  "-val-warn-copy-indeterminate=[warn when a statement of the specified functions copies a value that may be indeterminate]:funs:_funs"
  "-val-warn-undefined-pointer-comparison=[warn on pointer comparisons]:warn:(all pointer none)"
  "-undefined-pointer-comparison-propagate-all[undefined pointer comparisons always returns {0; 1}]"
  {,-no}"-val-warn-left-shift-negative[emit alarms when left-shifting negative integers]"
  "-val-show-trace[compute and display execution traces together with alarms]"
  "-val-reduce-on-logic-alarms[undocumented]"

# value_precision
  "-wlevel=[number of loop iterations before widening (defaults to 3)]:integer"
  "-val-ilevel=[sets of integers are represented as sets up to <n> elements (defaults to 8)]:integer"
  "-slevel=[superpose up to <n> states when unrolling control flow]:integer"
  "-slevel-function=[override slevel for the given functions]:funmap"
  "-plevel=[use <n> as the precision level for arrays accesses (defaults to 200)]:integer"
  "-val-slevel-merge-after-loop=[merge the different execution paths that originate from the body of a loop]:funs:_funs"
  "-val-subdivide-non-linear=[split up to <n> times the value of the variables that appear multiple times in an expression]:integer"
  "-remove-redundant-alarms[remove redundant alarms after the analysis]"
  "-eva-oracle-depth=[Maximum number of successive uses of the oracle by the domain for the evaluation of an expression]:integer"
  "-eva-reduction-depth=[Maximum number of successive backward reductions that the domain may initiate]:integer"

# value_perf
  "-memexec-all[speed up analysis by not recomputing functions already analyzed in the same context]"
  "-no-results-function=[do not record the values obtained for the statements of function f]:funs"
  "-no-results[do not record values for any of the statements of the program]"

# value_builtins
  "-val-builtin=[use Frama-C builtin]:builtins:_builtins"

# value_messages
  "-value-verbose=[level of verbosity for plug-in value analysis (default to 1)]:integer"
  "-value-debug=[level of debug for plug-in value analysis (default to 0)]:integer"
  "-value-msg-key=[enables message display for value categories]:key:_value_msg_key"
  "-no-val-show-progress[show progression messages during analysis]"
  "-val-show-time=[prints the time spent analyzing function calls, when it exceeds <n> seconds]:integer"
  "-val-show-perf[compute and shows a summary of the time spent analyzing function calls]"
  "-val-show-slevel=[period for showing consumption of the alloted slevel during analysis]:integer"
  "-val-print-callstacks[when printing a message, also show the current call stack]"

# value_interpreter
  "-val-interpreter-mode[interpreter mode]"
)

# -----------------------------------------------------------------------------
#                              Metrics
# -----------------------------------------------------------------------------

metrics_parameters=(

  "-metrics-ast=[apply metrics to Cabs, CIL AST, or ACSL specs]:target:(cabs cil acsl)"
  "-metrics"{,-no}"-by-function[also compute metrics on a per-function basis]"
  "-metrics-cover=[compute an overapproximation of the functions reachable from f1,..,fn]:funs:_funs"
  "-metrics"{,-no}"-libc[show functions from the Frama-C stdlib in the results]"
  "-metrics-output=[print some metrics into a file (extension defines the format)]:file:_files"
  "-metrics"{,-no}"-value-cover[estimate value analysis coverage w.r.t. to reachable syntactic definitions]"

# metrics output
  "-metrics"{,-no}"-by-function-print[print results for option -metrics-by-function]"
  "-metrics-debug=[level of debug for plug-in metrics (default to 0)]:integer"
  "-metrics"{,-no}"-print[print results for option -metrics]"
  "-metrics"{,-no}"-print-value-cover[print results for option -metrics-value-cover]"
)

# -----------------------------------------------------------------------------
#                              Main auto-complete
# -----------------------------------------------------------------------------


value_arguments=()

value () {
  if containsElement "-val" "${words[@]}"; then
    value_arguments=( "${value_parameters[@]}" )
  else
    value_arguments=(
      "-val[computes variation domains for the variables of the program]"
    )
  fi
}

metrics_arguments=()

metrics () {
  if containsElement "-metrics" "${words[@]}"; then
    metrics_arguments=( "${metrics_parameters[@]}" )
  else
    metrics_arguments=(
      "-metrics[activate metrics computation]"
    )
  fi
}

_frama-c () {
  value;
  metrics;
  _arguments \
    "*:file:_files -g '*.(h|c|i|cpp)' "          \
    ${analysis_options}                          \
    ${kernel_arguments}                          \
    ${value_arguments}                           \
    ${metrics_arguments}
}

_frama-c "$@"
