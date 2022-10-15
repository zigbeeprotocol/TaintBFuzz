/*@ lemma div_def: \forall integer i; 0<= i - 2*(i/2) <= 1; */

/*@
  predicate sorted{L}(int* arr, int length) =
  \forall integer i,j; 0<=i<=j<length ==> arr[i] <= arr[j];
*/

/*@ predicate Swap{L1,L2}(int a[], integer i, integer j) =
      \at(a[i],L1) == \at(a[j],L2) &&
      \at(a[j],L1) == \at(a[i],L2) &&
      \forall integer k; k != i && k != j
          ==> \at(a[k],L1) == \at(a[k],L2);
  @*/

/*@ inductive Permut{L1,L2}(int a[], integer l, integer h) {
     case Permut_refl{L}:
      \forall int a[], integer l, h; Permut{L,L}(a, l, h) ;
     case Permut_sym{L1,L2}:
       \forall int a[], integer l, h;
         Permut{L1,L2}(a,l, h) ==> Permut{L2,L1}(a, l, h) ;
     case Permut_trans{L1,L2,L3}:
       \forall int a[], integer l, h;
         Permut{L1,L2}(a, l, h) && Permut{L2,L3}(a, l, h) ==>
           Permut{L1,L3}(a,l, h) ;
     case Permut_swap{L1,L2}:
       \forall int a[], integer l, h, i, j;
          l <= i <= h && l <= j <= h && Swap{L1,L2}(a,i, j) ==>
        Permut{L1,L2}(a,l, h) ;
    }
  @*/

/*@
  requires length >= 0;
  requires \valid_range(arr, 0, length);
  requires sorted(arr,length);

  assigns \nothing;

  behavior exists:
  assumes \exists integer i; 0<=i<length && arr[i] == query;
  ensures arr[\result] == query;

  behavior not_exists:
  assumes \forall integer i; 0<=i<length ==> arr[i] != query;
  ensures \result == -1;
*/
int find_array(int* arr, int length, int query) {
  int low = 0;
  int high = length - 1;
  /*@
    loop invariant 0 <= low;
    loop invariant high < length;
    loop invariant \forall integer i; 0 <= i < low ==> arr[i] < query;
    loop invariant \forall integer i; high < i < length ==> arr[i] > query;
    loop variant high - low;
   */
  while (low <= high) {
    int mean = low + (high -low) / 2;
    //@ assert low <= mean <= high;
    if (arr[mean] == query)
      // @ for not_exists: assert \false;
      return mean;
    if (arr[mean] < query)
      low = mean + 1;
    else
      high = mean - 1;
  }
  return -1;
}

/*@
  requires \valid(a+(low..high-1));
  requires low < high;
  ensures \forall integer i; low <= i < high ==> a[i] >= a[\result];
  ensures low <= \result < high;
  assigns \nothing;
*/
int index_min(int* a, int low, int high) {
  if (low >= high) return low;
  int idx = low;
  int i = low+1;
  /*@ loop invariant low+1<=i<=high;
    loop invariant low <= idx < high;
    loop invariant \forall integer j; low <= j < i ==> a[j] >= a[idx];
   */
  while(i < high) {
    if (a[i] < a[idx])
      idx = i;
    i++;
  }
  return idx;
}

/*@ requires \valid(arr+i) && \valid(arr+j);
  assigns arr[i], arr[j];
  ensures Swap{Old,Here}(arr,i,j);
 */
void swap(int* arr, int i, int j) {
  int t = arr[i];
  arr[i] = arr[j];
  arr[j] = t;
}

/*@
  requires length >=0;
  requires \valid(arr + (0..length - 1));
  ensures sorted(arr,length);
  ensures Permut{Old,Here}(arr,0,length -1);
  //assigns arr[0..length -1];
*/
void min_sort(int* arr, int length) {
  /*@
    loop invariant 0<=i<=length;
    loop invariant sorted(arr,i);
    loop invariant \forall integer j,k;
    0 <= j < i <= k < length ==> arr[j] <= arr[k];
    loop invariant Permut{Pre,Here}(arr,0,length -1);
   */
  for(int i = 0; i < length; i++) {
    int min = index_min(arr,i,length);
    // @ assert \forall integer j; i<=j<length ==> arr[min]<=arr[j];
    swap(arr,i,min);
    // @ assert \forall integer j; i<=j<length ==> arr[i] <= arr[j];
  }
}

#if 0
/*@ inductive is_heap{L}(int* arr, integer length, integer root) {
  case leaf{L}:
  \forall int* arr, integer length, integer root;
  0<= root < length ==> 2*root + 1 >= length ==> is_heap{L}(arr,length,root);

  case node{L}:
  \forall int* arr, integer length, integer root;
  0<= root ==>
  (2*root + 1 < length ==>
    arr[root] >= arr[2*root+1] && is_heap(arr,length,2*root+1)) ==>
  (2*root + 2 < length ==>
    arr[root] >= arr[2*root+2] && is_heap(arr,length,2*root+2)) ==>
  is_heap(arr,length,root);
}
 */

/*@ predicate is_quasi_heap{L}(int* arr, integer length, integer root) =
  0<= root < length && (2* root + 1 < length ==> is_heap(arr,length,2*root+1))
  && (2*root + 2 < length ==> is_heap(arr,length,2*root+2));
*/

/*@ axiomatic sub_heap_loc {
  logic set<int> sub_heap_loc(int* arr, integer length, integer root);
  axiom empty: \forall int* arr, integer length, integer root;
  root < 0 || root >= length ==> sub_heap_loc(arr,length, root) == \empty;
  axiom node: \forall int* arr, integer length, integer root;
  0<=root<length ==> sub_heap_loc(arr,length,root) ==
  \union(arr[root],
         sub_heap_loc(arr,length,2*root+1),
         sub_heap_loc(arr,length,2*root+2));
}
*/


/*@ requires \valid(arr + (0..length - 1));
    requires is_quasi_heap(arr,length,root);
    ensures is_heap(arr,length,root);
    assigns sub_heap_loc(arr,length,root);
 */
void down_heap(int* arr, int length, int root) {
  int next = 2 * root + 1;
  while (next < length) {
    if (next + 1 < length && arr[next] < arr[next+1]) next++;
    if (arr[root] < arr[next]) {
        int t = arr[root];
        arr[root] = arr[next];
        arr[next] = t;
        root = next;
        next = 2 * root + 1;
      }
    else break;
  }

}

/*@ requires \valid(arr + (0..length -1));
    ensures  is_heap(arr,length,0);
    assigns arr[0..length -1];
*/
void make_heap(int* arr,int length) {
  int n = (length -1)/2 + 1;
  /*@ loop invariant \forall integer i; n<i<length ==> is_heap(arr,length,i);
   */
  while (n >=1) {
    down_heap(arr,length,n);
    n--;
  }
}

/*@ requires \valid(arr + (0..length - 1));
  ensures sorted(arr,length);
  ensures Permut{Pre,Post}(arr,0,length -1);
  assigns arr[0..length -1];
*/
void heap_sort(int* arr, int length) {
  make_heap(arr,length);
  for(int n = length; n>1; n--) {
    int t=arr[0];
    arr[0]=arr[n];
    arr[n]=arr[0];
    down_heap(arr,length,0);
  }
}
#endif
