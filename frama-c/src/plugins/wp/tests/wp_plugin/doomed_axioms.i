/* run.config
   OPT: -wp-smoke-tests
 */

/* run.config_qualif
   OPT: -wp-smoke-tests
*/

/*@ axiomatic CFG {
  predicate P(integer x);
  predicate Q(integer x);
  predicate R(integer x);
  axiom init: P(0) && Q(0) && R(0);
  axiom loop1: \forall integer n; P(n) ==> Q(n+1);
  axiom loop2: \forall integer n; Q(n) ==> R(n+1);
  axiom loop3: \forall integer n; R(n) ==> !P(n);
  }*/


int foo(int x)
{
  int n = 0;
  /*@
    loop invariant A: P(n);
    loop invariant B: Q(n);
    loop invariant C: R(n);
    loop assigns n ;
  */
  while (x>0) {
    n++;
  }
  return n;
}
