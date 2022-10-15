/* run.config
   OPT:
   OPT: -wp-smoke-tests
 */

/* run.config_qualif
   OPT: -wp-smoke-tests
*/

/*@ axiomatic CFG {
  predicate ASSUMES(integer x,integer y);
  predicate REQUIRES(integer x,integer y);
  predicate ENSURES(integer x,integer y);
  }*/

/*@
  requires REQUIRES(0,x);
  requires x < 0 ;
  behavior A:
    assumes  ASSUMES(1,x);
    requires REQUIRES(1,x);
    requires 2 < x ;
  behavior B:
    assumes  ASSUMES(2,x);
    requires REQUIRES(2,x);
 */
int foo(int x)
{
  x++;
  return x;
}


/*@ requires x > 0; ensures \result == x+1 ; */
int bar(int x)
{
  return x+1;
}

/*@ requires x > 0; requires x < -4 ; ensures \result == x-1 ; */
int buzz(int x)
{
  return x-1;
}
