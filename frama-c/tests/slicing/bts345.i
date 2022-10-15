/* run.config
   STDOPT: +"-slice-return call_top -main call_top -then-on 'Slicing export' -set-project-as-default -print -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -check "
   STDOPT: +"-slice-return top      -main top -then-on 'Slicing export' -set-project-as-default -print -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -check "
   STDOPT: +"-slice-return top      -main call_top -then-on 'Slicing export' -set-project-as-default -print -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -check "
   STDOPT: +"-slice-return called_by_top -main top -then-on 'Slicing export' -set-project-as-default -print -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -check "
   STDOPT: +"-slice-return called_by_top -main call_top -then-on 'Slicing export' -set-project-as-default -print -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -check "
*/

int called_indirectly_by_top (int x) {
  x++ ;
  return x ;
}

int called_by_top (int x) {
  x++ ;
  int z = called_indirectly_by_top (x) ;
  return z ;
}

int top (int x, ...) {
  x++ ;
  int z = called_by_top (x) ;
  return z;
}

int call_top (int y) {
  y++;
  int z = top (y) ;
  return z ;
}
