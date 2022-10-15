/*@ predicate p(integer n) = \forall integer i; 0 <= i < n ==> 2 * i < n * i + 1; */

int main(void) {
  /*@ assert p(2); */
}
