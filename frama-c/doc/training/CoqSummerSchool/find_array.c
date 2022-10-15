/*@ lemma div_pos: \forall integer i; 0<=i ==> 0<= i/2 <= i; */

/*@
  predicate sorted{L}(int* arr, integer length) =
  \forall integer i,j; 0<=i<=j<length ==> arr[i] <= arr[j];
*/

/*@ requires \valid(arr+(0..length-1));
    requires sorted(arr,length);
    requires length > 0;
    assigns \nothing;
    behavior exists:
    assumes \exists integer i; 0<=i<length && arr[i] == query;
    ensures 0<=\result<length && arr[\result] == query;
    behavior not_exists:
    assumes \forall integer i; arr[i] != query;
    ensures \result == -1;
 */
int find_array(int* arr, int length, int query) {
  int low = 0;
  int high = length - 1;
  /*@
    loop invariant 0<=low<=high+1<=length;
    loop invariant \forall integer i; 0<=i<low ==> arr[i]<query;
    loop invariant \forall integer i; high<i<length ==> arr[i]>query;
    loop variant high - low;
   */
  while (low <= high) {
    int mean = low + (high -low) / 2;
    /*@ assert low<=mean<=high; */
    if (arr[mean] == query) return mean;
    if (arr[mean] < query) low = mean + 1;
    else high = mean - 1;
  }
  return -1;
}

/*
Local Variables:
compile-command: "frama-c -jessie find_array.c"
End:
*/
