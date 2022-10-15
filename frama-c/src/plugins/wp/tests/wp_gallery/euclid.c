/*
  run.config
  DONTRUN:
 */

/*
  run.config_qualif
  OPT: -wp-rte -wp-smoke-tests -wp-driver %{dep:@PTEST_DIR@/euclid.wp}
*/

/*@
  axiomatic Euclid {
    logic integer gcd(integer a, integer b);
  }
*/


#include <limits.h>

/*@
  requires \abs(a) <= INT_MAX ;
  requires \abs(b) <= INT_MAX ;
  assigns \nothing;
  ensures \result == gcd(a,b);
*/

int euclid_gcd(int a, int b)
{
  int r;
  /*@
    loop assigns a, b, r;
    loop invariant gcd(a,b) == \at( gcd(a,b), Pre );
    loop variant \abs(b);
  */
  while( b != 0 ) {
    r = b ;
    b = a % b ;
    a = r ;
  }
  return a < 0 ? -a : a;
}
