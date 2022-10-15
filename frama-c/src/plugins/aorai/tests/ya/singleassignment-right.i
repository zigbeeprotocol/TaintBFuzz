/* run.config*
   OPT: -aorai-automata %{dep:@PTEST_DIR@/@PTEST_NAME@.ya} -aorai-test-number @PTEST_NUMBER@ @PROVE_OPTIONS@
*/

void main(int *x, int *y)
{
  int t = *x;
  *x = *y;
  *y = t;
}
