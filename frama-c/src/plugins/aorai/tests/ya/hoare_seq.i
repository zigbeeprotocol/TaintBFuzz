/* run.config*
OPT: -aorai-automata %{dep:@PTEST_DIR@/@PTEST_NAME@.ya} -aorai-acceptance -aorai-test-number @PTEST_NUMBER@ @PROVE_OPTIONS@
*/

void f(void) { }

/*@ behavior bhv:
    assumes c > 0;
    ensures \result == 0;
*/
int main(int c) {
  if (c <= 0) { f (); }
  return 0;
}
