/*@
  predicate sorted{L}(int* arr, integer length) =
  \forall integer i,j; 0<=i<=j<length ==> arr[i] <= arr[j];

  predicate swap{L1,L2}(int* arr, integer i, integer j) =
  \at(arr[i],L1) == \at(arr[j],L2) &&
  \at(arr[j],L1) == \at(arr[i],L2) &&
  \forall integer k; i!=k && j!=k ==> \at(arr[k],L1) == \at(arr[k],L2);

  axiomatic Permut {
    predicate permut{L1,L2}(int* arr, integer length);
    axiom permut_refl{L}: \forall int* arr, integer length; permut{L,L}(arr,length);
    axiom permut_swap{L1,L2}: \forall int* arr,
    integer i,j,length; 0<=i<length && 0<=j<length &&
    swap{L1,L2}(arr,i,j) ==> permut{L1,L2}(arr,length);
    axiom permut_trans{L1,L2,L3}: \forall int* arr,
    integer length;
    permut{L1,L2}(arr,length) ==> permut{L2,L3}(arr,length) ==>
    permut{L1,L3}(arr,length);
  }
*/

/*@ requires \valid_range(a,low,high-1);
    requires low<high;
    assigns \nothing;
    ensures \forall integer i; low<=i<high==> a[\result]<=a[i];
    ensures low<=\result<high;
 */
int index_min(int* a, int low, int high);

/*@ requires \valid(arr+i) && \valid(arr+j);
  ensures swap{Old,Here}(arr,i,j);
 */
void swap(int* arr, int i, int j);

int index_min(int* a, int low, int high) {
  if (low >= high) return low;
  int idx = low;
  int i = low+1;
  /*@ loop invariant low <= i <= high;
    loop invariant \forall integer j;
    low<=j<i ==> a[idx]<=a[j];
    loop invariant low <= idx < i;
    loop variant high -i;
   */
  while(i < high) {
    if (a[i] < a[idx])
      idx = i;
    i++;
  }
  return idx;
}

void swap(int* arr, int i, int j) {
  int t = arr[i];
  arr[i] = arr[j];
  arr[j] = t;
}

/*@ requires \valid_range(arr,0,length-1) && length > 0;
    behavior sorted: ensures sorted(arr,length);
    behavior permut: ensures permut{Old,Here}(arr,length);
 */
void min_sort(int* arr, int length) {
  /*@
    loop invariant 0<=i<=length;
    for sorted: loop invariant sorted(arr,i);
    for permut: loop invariant permut{Pre,Here}(arr,length);
    for sorted: loop invariant \forall integer j,k; 0<=j<i<=k<length ==>
    arr[j]<=arr[k];
    loop variant length - i;
   */
  for(int i = 0; i < length; i++) {
    int min = index_min(arr,i,length);
    /*@ for sorted: assert \forall integer j,k; 0<=j<i<=k<length ==>
     arr[j]<=arr[min]<=arr[k];
    */
    swap(arr,i,min);
    /*@ for sorted: assert \forall integer j,k; 0<=j<i<=k<length ==>
     arr[j]<=arr[i]<=arr[k];
    */
  }
}
/*
Local Variables:
compile-command: "frama-c -jessie sort_array.c"
End:
*/
