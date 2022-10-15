/*@
  predicate sorted{L}(int* arr, integer length) =
  \forall integer i,j; 0<=i<=j<length ==> arr[i] <= arr[j];
*/

/*@ predicate swap{L1,L2}(int* arr, integer i, integer j) =
  \at(arr[i], L1) == \at(arr[j], L2) &&
  \at(arr[j], L1) == \at(arr[i], L2) &&
  \forall integer k; k!= i && k!= j ==> \at(arr[k],L1) == \at(arr[k],L2);
 */

/*@ inductive permut{L1,L2}(int* arr, integer length) {
  case perm_refl{L}: \forall int* arr, integer length; permut{L,L}(arr,length);
  case perm_swap{L1,L2}:
    \forall int* arr, integer length,i,j;
       0<=i<length && 0<= j < length ==>
       swap{L1,L2}(arr,i,j) ==> permut{L1,L2}(arr,length);
  case perm_trans{L1,L2,L3}:
    \forall int* arr, integer length;
    permut{L1,L2}(arr,length) ==> permut{L2,L3}(arr,length) ==>
    permut{L1,L3}(arr,length);
}
*/

/*@ lemma permut_one_step{L1,L2,L3}:
    \forall int* arr, integer length,i,j;
     0<=i<length && 0<= j < length ==>
    permut{L1,L2}(arr,length) ==> swap{L2,L3}(arr,i,j) ==>
    permut{L1,L3}(arr,length);
*/

/*@ lemma sorted_swap{L1,L2}:
  \forall int* arr, integer length,ind;
  length<=ind && sorted{L1}(arr,length) &&
  swap{L1,L2}(arr,length,ind) &&
  \at(arr[length-1],L2) <= \at(arr[length],L2) ==>
     sorted{L2}(arr,length+1);
*/

int index_min(int* a, int low, int high);

void swap(int* arr, int i, int j);

/*@ requires \valid(a+(low..high -1));
  requires low < high;
  ensures \forall integer j; low <= j < high ==> a[\result] <= a[j];
  ensures low <= \result < high;
  assigns \nothing;
 */
int index_min(int* a, int low, int high) {
  if (low >= high) return low;
  int idx = low;
  int i = low+1;
  /*@ loop invariant low <= i <= high;
      loop invariant low <= idx < high;
      loop invariant \forall integer j; low <= j < i ==> a[idx] <= a[j];
   */
  while(i < high) {
    if (a[i] < a[idx])
      idx = i;
    i++;
  }
  return idx;
}
/*@
  requires \valid(arr+i) && \valid(arr+j);
  ensures swap{Old,Here}(arr,i,j);
  assigns arr[i],arr[j];
 */
void swap(int* arr, int i, int j) {
  int t = arr[i];
  arr[i] = arr[j];
  arr[j] = t;
}

/*@ requires \valid_range(arr,0,length - 1);
    requires length > 0;
    ensures sorted(arr,length);
    ensures permut{Old,Here}(arr,length);
 */
void min_sort(int* arr, int length) {
  /*@ loop invariant 0 <= i <= length;
    loop invariant sorted(arr,i);
    loop invariant permut{Pre,Here}(arr,length);
    loop invariant \forall integer j,k; 0<=j<i<=k<length ==> arr[j] <= arr[k];
   */
  for(int i = 0; i < length; i++) {
    int min = index_min(arr,i,length);
    /*@ assert \forall integer j; i<=j<length ==> arr[min]<=arr[j]; */
    /*@ assert \forall integer j; 0<=j<i ==> arr[j]<=arr[min]; */
    swap(arr,i,min);
    /*@ assert \forall integer j;  i<=j<length ==> arr[i]<=arr[j]; */
    /*@ assert \forall integer j; 0<=j<i ==> arr[j]<=arr[i]; */
  }
}

/*
Local Variables:
compile-command: "frama-c -jessie sort_array_proved.c"
End:
*/
