/* run.config
   STDOPT: +"-slice-assert main -then-on 'Slicing export' -set-project-as-default -print -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -check"
*/
int main (int c) {
  if (c)
    while (1) { ; }
  //@ assert c == 0;
  return c;
}
