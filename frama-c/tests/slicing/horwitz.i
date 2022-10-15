/* run.config
 LIBS: libSelect
 MODULE: @PTEST_NAME@
   OPT: @EVA_OPTIONS@ -deps -slicing-level 0
*/

/* bin/toplevel.opt -deps -eva %{dep:@PTEST_DIR@/@PTEST_NAME@.c} */
/* bin/toplevel.opt -deps -pdg-debug -pdg %{dep:@PTEST_DIR@/@PTEST_NAME@.c} */
/* cf aussi @PTEST_DIR@/@PTEST_NAME@.ml */

int add (int a, int b) {
  return a+b;
}
void incr (char * pi) {
  *pi = add (*pi, 1);
}
int A (int x, char * py) {
  x = add (x, *py);
  incr (py);
  /*@ slice pragma expr x;*/
  return x;
}
int main (void) {
  int s = 0;
  char i = 1;
  while (i < 11) {
    s = A (s, &i);
  }
  return s;
}
