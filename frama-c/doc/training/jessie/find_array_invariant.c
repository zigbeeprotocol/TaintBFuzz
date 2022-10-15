/*@
  loop invariant 0 <= low;
  loop invariant high < length;
  loop invariant \forall integer i;
    0 <= i < low ==> arr[i] < query;
  loop invariant \forall integer i;
    high < i < length ==> arr[i] > query;
*/
