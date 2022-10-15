/* run.config
   STDOPT: +"-eva -slice-assert f -slicing-level 0 -then-on 'Slicing export' -set-project-as-default -print -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -check -no-eva"
*/
/*@ requires a > 0; */
int f(int a) {
  int b = 2 * a;
  /*@ assert a < b; */
  return 42;
}

int main () {
  f(10);
  return 0;
}
