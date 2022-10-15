/* run.config
* STDOPT: +"-eva-no-builtins-auto -slicing-level 0 -slice-return uncalled -no-slice-callers  -then-on 'Slicing export' -set-project-as-default -print -check -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -check"
* STDOPT: +"-eva-no-builtins-auto -slicing-level 2 -slice-return main -then-on 'Slicing export' -set-project-as-default -print -check -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -check"
* STDOPT: +"-eva-no-builtins-auto -slicing-level 2 -slice-return strlen -then-on 'Slicing export' -set-project-as-default -print -check -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -check"
*
*
*
*
*
*
*/

int uncalled (int x) {
  return x+1;
}

int strlen(char* p ) {
  char* q ;
  int k = 0;

  for (q = p; *q ; q++) k++ ;

  return k;
}

int main (char *p_str[], int i ) {
  return strlen (p_str[i]);
}
