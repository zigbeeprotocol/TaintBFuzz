/* run.config
   DONTRUN:
*/

/* run.config_qualif
   OPT: -wp-rte -wp-smoke-tests
 */


/*@
  requires size >= 0;
  requires \valid(t + (0 .. size-1));
  requires ∀ integer i, integer j; 0 <= i <= j < size ==> t[i] <= t[j];
  ensures Result: -1 <= \result < size;
  ensures Found: \result >= 0 ==> t[\result] == key;
  ensures NotFound: \result == -1 ==> ∀ integer i; 0 <= i < size ==> t[i] != key;
*/
int binary_search(int * t, int size, int key)
{
  int lo, hi, mid;
  lo = 0; hi = size - 1;
  /*@
    loop assigns lo, hi, mid;
    loop invariant Range: 0 <= lo && hi < size;
    loop invariant Left: ∀ integer i; 0 <= i < lo ==> t[i] < key;
    loop invariant Right: ∀ integer i; hi < i < size ==> t[i] > key;
    loop variant hi - lo;
   */
  while (lo <= hi) {
    mid = lo + (hi - lo) / 2;
    if (key == t[mid]) return mid;
    if (key < t[mid]) hi = mid - 1; else lo = mid + 1;
  }
  return -1;
}
