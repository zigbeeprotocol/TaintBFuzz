/* run.config
   STDOPT: +"-deps -slice-return main -then-on 'Slicing export' -set-project-as-default -print -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -check -no-deps"
*/
int main() {
  volatile int a=0,b,c;
  if (a)
    {a = 1;

  while (1) {
    a++;
    };
  return 0;}
}
