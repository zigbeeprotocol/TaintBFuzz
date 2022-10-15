/* run.config
   COMMENT: extended quantifiers (sum, product, numof)
*/

#include <limits.h>

int main(void) {
  unsigned long x = UINT_MAX;
  int y = 10;

  /*@ assert \sum(2, 10, \lambda integer k; 2 * k) == 108; */;
  /*@ assert \sum(2, 35, \lambda integer k; ULLONG_MAX) != 0; */;
  /*@ assert \sum(10, 2, \lambda integer k; k) == 0; */;
  /*@ assert \sum(x * x, 2, \lambda integer k; k) == 0; */;
  /*@ assert \sum(ULLONG_MAX - 5, ULLONG_MAX, \lambda integer k; 1) == 6; */;
  /*@ assert \sum(INT_MAX, INT_MAX, \lambda integer k; k) + 1 > INT_MAX; */
  /*@ assert \let x = (0 == 0) ? 1 : 10;
    @        \sum (x, 10, \lambda integer k; INT_MIN) < 0; */

  /*@ assert \numof(2, 10, \lambda integer k; k - 2 >= 0) == 9; */;
  /*@ assert \numof(UINT_MAX - 5, UINT_MAX, \lambda integer k; k % 2 == 1)
    @        == 3; */
  ;

  /*@ assert \product(1, 100, \lambda integer k; k) >= 3628800; */;
  /*@ assert \product(1, 10, \lambda integer k; k) == 3628800; */;
  /*@ assert \product(-10, 10, \lambda integer k; k) == 0; */;
  /*@ assert \product(-20, -1, \lambda integer k; 2 * k)
    @     == \product(1, 20, \lambda integer k; 2 * k); */
  ;

  return 0;
}
