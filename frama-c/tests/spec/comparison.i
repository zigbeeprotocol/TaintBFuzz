/* run.config
   MODULE: @PTEST_NAME@
   OPT: -no-autoload-plugins
*/

/*@ predicate foo(boolean a, boolean b) = a == b; */

void main(void) {
  int x = 0, y = 0;
  long z = 0L;
  /*@ assert x == y; */
  /*@ assert x == z; */
  /*@ assert (long)x == z; */
  /*@ assert foo(x==y,x==z); */
  /*@ assert foo(z==(long)y, y == x); */
}
