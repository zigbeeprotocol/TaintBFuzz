/* run.config*
   OPT: -aorai-automata %{dep:@PTEST_DIR@/@PTEST_NAME@.ya} -aorai-test-number @PTEST_NUMBER@ @PROVE_OPTIONS@
*/

int f(void);

int main(void) {
  return f();
}
