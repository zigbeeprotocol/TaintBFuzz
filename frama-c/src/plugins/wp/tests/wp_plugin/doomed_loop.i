/* run.config
   OPT: -wp-smoke-tests
 */

/* run.config_qualif
   OPT: -wp-smoke-tests
*/

/*@ axiomatic CFG {
  predicate P(integer x);
  }*/


int foo(int x)
{
  int n = 0;
  /*@
    loop invariant A: P(n);
    loop invariant B: !P(n);
    loop assigns n ;
  */
  while (x>0) {
    n++;
  }
  return n;
}
