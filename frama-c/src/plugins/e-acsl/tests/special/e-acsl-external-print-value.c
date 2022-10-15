/* run.config_dev
   MACRO: ROOT_EACSL_GCC_OPTS_EXT --assert-print-data --external-print-value %{dep:@PTEST_DIR@/e-acsl-external-print-value-fct.c}
*/

int main() {
  int value = 1;
  //@ check \let x = value; \false;
  return 0;
}
