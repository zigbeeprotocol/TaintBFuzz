/* run.config*
   OPT: -aorai-automata %{dep:@PTEST_DIR@/@PTEST_NAME@.ya} -aorai-test-number @PTEST_NUMBER@ @PROVE_OPTIONS@
*/

void f(void) {}

void g(void) {
  for (int i = 0; i < 1; i++) ;
}

void h(void) {
  g();
  g();
}

int main() {
  f();
  g();
  h();
}
