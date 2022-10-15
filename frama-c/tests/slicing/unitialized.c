/* run.config
   STDOPT: +"-slice-pragma g -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-slice-assert g -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-slice-assert main -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
   STDOPT: +"-slice-return g -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "
 */
#ifdef __FRAMAC__
//@ assigns \result \from \nothing;
int printf(const char*, int y);
#endif


int X1, X2 ;
void f1() {
  int x1;
  x1 = 123;
  X1 = x1 ;
}

void f2() {
  int x2;
  x2 = 12345;
  X2 = x2 ;
}

int g() {
  int y ;
  /* Note: y is not initialised by g. */
  /* Note: GCC without optimization gives X1 == y. */
  printf ("%d\n", y);
  //@slice pragma expr y ;
  //@assert X1 == y ;
  return y;
}

int main() {
  int r;
  f1();
  f2();
  r = g();
  /* Note: GCC without optimization gives X2 != y. */
  //@assert X2 != r ;
  return 0;
}
