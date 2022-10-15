/* run.config*
   OPT: -aorai-automata %{dep:@PTEST_DIR@/@PTEST_NAME@.ya} -aorai-acceptance -main f -aorai-test-number @PTEST_NUMBER@ @PROVE_OPTIONS@
*/

int f(int x) {
  return x;
}
