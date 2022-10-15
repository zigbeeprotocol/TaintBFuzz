/* run.config
MACRO: RM_TMP_DIR rm -rf make-for-make-wrapper.parse make-for-make-wrapper.eva
   NOFRAMAC: testing frama-c-script
   COMMENT: in case of errors, remove the 'grep' part to get the full output
   PLUGIN: eva,from,inout,metrics,nonterm,report,scope,variadic
   EXECNOW: LOG make-wrapper.res LOG make-wrapper.err (cd @PTEST_DIR@ && touch %{dep:make-wrapper2.c} && touch %{dep:make-wrapper3.c} && @RM_TMP_DIR@ && FRAMAC='%{bin:frama-c} @PTEST_DEFAULT_OPTIONS@ @PTEST_LOAD_OPTIONS@' PTESTS_TESTING=1 %{bin:frama-c-script} make-wrapper --make-dir . -f %{dep:make-for-make-wrapper.mk} | grep -A999999 "make-wrapper recommendations" && @RM_TMP_DIR@) > @PTEST_RESULT@/make-wrapper.res 2> @PTEST_RESULT@/make-wrapper.err
*/


int defined(int a);

int specified(int a);

int external(int a);

int large_name_to_force_line_break_in_stack_msg(void) {
  return large_name_to_force_line_break_in_stack_msg();
}

int rec(void) {
  return large_name_to_force_line_break_in_stack_msg();
}

int main() {
  int a = 42;
  a = rec();
  a = defined(a);
  a = specified(a);
  a = external(a);
}
