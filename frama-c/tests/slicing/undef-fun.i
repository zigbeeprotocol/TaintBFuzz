/* run.config
 STDOPT: +"-slice-undef-functions -slice-return f -then-on 'Slicing export' -set-project-as-default -print  -then -print -ocode @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i -then @PTEST_RESULT@/ocode_@PTEST_NUMBER@_@PTEST_NAME@.i  "



 */

int G;

/*@ assigns \result \from a;
    assigns G \from b;
*/
int f (int a, int b);

int main (int x, int y) {
  x += 1;
  y += 2;
  x = f (x, y);
  return x;
}
