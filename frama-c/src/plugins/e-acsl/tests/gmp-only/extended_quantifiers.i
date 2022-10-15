/* run.config
   COMMENT: extended quantifiers (sum, product, numof)
*/

int main(void) {

  /*@ assert \sum(2, 10, \lambda integer k; 2 * k) == 108; */;
  /*@ assert \sum(1, 10, \lambda integer k; 1) == 10; */;

  /*@ assert \numof(2, 10, \lambda integer k; k - 2 >= 0) == 9; */;

  /*@ assert \product(1, 10, \lambda integer k; k) == 3628800; */;
  /*@ assert \product(-10, 10, \lambda integer k; k) == 0; */;
  ;

  return 0;
}
