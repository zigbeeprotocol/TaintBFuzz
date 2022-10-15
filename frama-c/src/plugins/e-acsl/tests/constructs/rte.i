/* run.config
 * COMMENT: Check that the RTE checks are generated for every part of a
 * behavior, and are generated at the right place.
 */

/*@
  requires 1 % a == 1;
  ensures 1 % b == 1;

  behavior bhvr:
    assumes 1 % c == 1;
    requires 1 % d == 1;
    requires (1 % f == 1) || (1 % g == 1);
    requires (1 % h == 1) && (1 % i == 1);
    requires \let var = 1; var % j == 1;
    requires \forall integer var; 0 <= var < k ==> var % k == var;
    requires \exists integer var; 0 <= var < l && var % l == var;
    ensures 1 % e == 1;
*/
void test(int a, int b, int c, int d, int e, int f, int g, int h, int i, int j,
          int k, int l) {}

int main(void) {
  test(2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13);
  return 0;
}
