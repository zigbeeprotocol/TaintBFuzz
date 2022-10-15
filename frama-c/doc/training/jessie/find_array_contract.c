/*@
  behavior exists:
  assumes \exists integer i;
          0<=i<length && arr[i] == query;
  ensures arr[\result] == query;

  behavior not_exists:
  assumes \forall integer i;
          0<=i<length ==> arr[i] != query;
  ensures \result == -1;
*/
