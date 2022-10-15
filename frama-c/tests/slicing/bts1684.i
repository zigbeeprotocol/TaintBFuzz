/* run.config
   STDOPT: +"-slice-calls main -then-on 'Slicing export' -set-project-as-default -print -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i"
*/
// bug about slicing CALLS TO MAIN function.
double d1, d2, d3;
int x1, x2, x3;
int main2 (void) {
  d1 = d2 * d3;
  x1 = x2 * x3;
  return 1;
}

int main (void) {
  return main2();
}
