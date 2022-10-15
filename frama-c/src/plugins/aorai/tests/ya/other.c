/* run.config*
   OPT: -aorai-automata %{dep:@PTEST_DIR@/@PTEST_NAME@.ya} -aorai-acceptance -aorai-test-number @PTEST_NUMBER@ @PROVE_OPTIONS@
*/

int x=0;

void f (void) { x=3; }

void g (void) { x=4; }

int main () {
  f();
  g();
  f();
  g();
  return x;
}
