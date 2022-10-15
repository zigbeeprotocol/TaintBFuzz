/* run.config*
MODULE: @PTEST_NAME@
OPT:
*/

void f() {
  int i = 0;
  /*@ loop assigns i; */
  while (i< 10) { i++; }

  while (i>0) { i--; }
}
