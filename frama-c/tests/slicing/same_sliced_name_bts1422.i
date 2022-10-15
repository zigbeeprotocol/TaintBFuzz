/* run.config
STDOPT: +"-main foo -slice-value y -then-on 'Slicing export' -set-project-as-default -print -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -check "
*/

int y;

void foo(int x);

void foo(int x) { x++; y++; }

void (*ptr)(int x) = &foo;
