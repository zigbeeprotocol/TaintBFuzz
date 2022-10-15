/* run.config
OPT: -aorai-automata %{dep:@PTEST_DIR@/@PTEST_NAME@.ya} -aorai-test-number @PTEST_NUMBER@ @PROVE_OPTIONS@
*/

void f(void) {}

void main(void) {
  while (1) f();
}
