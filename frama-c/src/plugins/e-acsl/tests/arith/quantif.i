/* run.config
   COMMENT: quantifiers
   STDOPT: +"-eva-min-loop-unroll=15"
*/

// Support predicates for some tests
//@ predicate p1(integer i, integer j, integer k) = 0 <= i < 10 && 1 < j <= 11 && 2 <= k <= 12;
//@ predicate p2(integer i, integer j, integer k) = 0 <= i <= j < k <= 10;
//@ predicate p3(integer i, integer j, integer k) = 0 <= i < j <= 10 && 1 < k < 11;
//@ predicate p4(integer i, integer j, integer k) = 0 <= i <= k <= 10 && 1 <= j < k;

int main(void) {

  // simple universal quantifications

  /*@ assert \forall integer x; 0 <= x <= 1 ==> x == 0 || x == 1; */
  /*@ assert \forall integer x; 0 < x <= 1 ==> x == 1; */
  /*@ assert \forall integer x; 0 <= x < 1 ==> x == 0; */

  /* // multiple universal quantifications */

  /*@ assert \forall integer x,y,z; 0 <= x < 2 && 0 <= y < 5 && 0 <= z <= y
    ==> x+z <= y+1; */

  // simple existential quantification

  /*@ assert \exists int x; 0 <= x < 10 && x == 5; */

  // mixed universal and existential quantifications

  /*@ assert \forall int x; 0 <= x < 10
    ==> x % 2 == 0 ==> \exists integer y; 0 <= y <= x/2 && x == 2 * y; */

  // quantifications inside quantifications

  /*@ assert \forall int x; 0 <= x < 10
    ==> (\forall int y; 10 <= y < 20 ==> x <= y) &&
        (\forall int y; -10 <= y < 0 ==> y <= x); */

  { // Gitlab issue #42
    int buf[10];
    unsigned long len = 9;
    /*@ assert \forall integer i; 0 <= i < 10 ==> \valid(buf+i); */
    /*@ assert \forall char i; 0 <= i < 10 ==> \valid(buf+i); */
    /*@ assert \forall integer i; 0 <= i < len ==> \valid(buf+i); */
    /*@ assert \forall integer i; 0 <= i <= len ==> \valid(buf+i); */
  }

  // Empty quantifications
  /*@ assert \forall integer x; 0 < x < 1 ==> \false; */
  /*@ assert ! \exists char c; 10 <= c < 10 && c == 10; */;
  /*@ assert
        \let u = 5;
        \forall integer x,y; 0 <= x < 2 && 4 < y < u ==> \false; */
  ;

  // Quantification with multiple binders (frama-c/e-acsl#127)
  /*@ assert forall_multiple_binders_1:
      \forall integer i,j,k;
      0 <= i < 10 && 1 < j <= 11 && 2 <= k <= 12 ==> p1(i,j,k); */
  /*@ assert forall_multiple_binders_2:
      \forall integer i,j,k;
      0 <= i <= j < k <= 10 ==> p2(i,j,k); */
  /*@ assert forall_multiple_binders_3:
      \forall integer i,j,k;
      0 <= i < j <= 10 && 1 < k < 11 ==> p3(i,j,k); */
  /*@ assert forall_multiple_binders_4:
      \forall integer i,j,k;
      0 <= i < 10 ==> 1 < j <= 11 ==> 2 <= k <= 12 ==> p1(i,j,k); */
  /*@ assert forall_unordered_binders:
    \forall integer i,j,k; 0 <= i <= k <= 10 && 1 <= j < k ==> p4(i,j,k); */

  /*@ assert exists_multiple_binders_1:
      \exists integer i,j,k;
      0 <= i < 10 && 1 < j <= 11 && 2 <= k <= 12 && p1(i,j,k); */
  /*@ assert exists_multiple_binders_2:
      \exists integer i,j,k;
      0 <= i <= j < k <= 10 && p2(i,j,k); */
  /*@ assert exists_multiple_binders_3:
      \exists integer i,j,k;
      0 <= i < j <= 10 && 1 < k < 11 && p3(i,j,k); */
  /*@ assert exists_unordered_binders:
      \exists integer i,j,k;
      0 <= i <= k <= 10 && 1 <= j < k && p4(i,j,k); */

  // Checking unsupported quantifications
  /*@ assert failed_invalid_guards:
      \forall integer i; 10 > i >= 0 ==> p1(i, 2, 2); */
  /*@ assert failed_unguarded_k:
      \forall integer i,j,k; 0 <= i < 10 && 1 < j <= 11 ==> p1(i,j,k); */
  /*@ assert failed_non_integer:
      \forall real i; 0 <= i < 10 ==> p1((integer)i, 2, 2); */
  /*@ assert failed_missing_lower_bound:
      \forall integer i; i < 10 ==> p1(i, 2, 2); */
  /*@ assert failded_missing_upper_bound:
      \forall integer i; 0 <= i ==> p1(i, 2, 2); */
  /*@ assert failed_invalid_upper_bound_1:
      \forall integer i,j; 0 <= i < j ==> p1(i, j, 2); */
  /*@ assert failed_invalid_upper_bound_2:
      \forall integer i,j; i < j && 0 <= i ==> p1(i, 2, 2); */
  /*@ assert failed_extra_constraint:
      \forall integer i,j; 0 <= i && i < j && i < 10 && 3 <= j < 5 ==> p1(i,j,2); */
  /*@ assert failed_multiple_upper_bounds:
      \forall integer i,j; 0 <= i < j && j < i && j <= 10 ==> p1(i,j,2); */
  /*@ assert multiple_linked_upper:
    \forall integer i,j,k; 0 <= i < k && 1 <= j < k && 2 <= k < 10 ==> p1(i,j,k); */
  /*@ assert multiple_guard:
    \forall integer i,j; 0 <= i < 10 && 2 <= i < 8 && 4 <= j < 6 ==> p1(i,j,2); */

  return 0;
}
