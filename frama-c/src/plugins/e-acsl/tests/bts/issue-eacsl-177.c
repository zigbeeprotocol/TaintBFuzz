/* run.config
   COMMENT: test for issue e-acsl 177
   STDOPT: +"-eva-unroll-recursive-calls 100"
*/

#include <limits.h>

/*@ logic integer f(integer n) =
    n <= INT_MAX+1 || n >= LONG_MAX+1 ? 0 : f(n + 1) + n; */

int main(void) {
  /*@ assert f(0) == 0; */;

  /*@ assert (\let n = (0 == 0) ? LONG_MAX : -1; f(n) != 0); */
}
