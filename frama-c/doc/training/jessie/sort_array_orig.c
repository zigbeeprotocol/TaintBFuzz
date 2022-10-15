//NOPP-BEGIN
/*@
  predicate sorted{L}(int* arr, integer length) =
  \forall integer i,j; 0<=i<=j<length ==> arr[i] <= arr[j];
*/
//NOPP-END
int index_min(int* a, int low, int high);

void swap(int* arr, int i, int j);

//NOPP-BEGIN
int index_min(int* a, int low, int high) {
  if (low >= high) return low;
  int idx = low;
  int i = low+1;
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
//NOPP-END
void min_sort(int* arr, int length) {
  for(int i = 0; i < length; i++) {
    int min = index_min(arr,i,length);
    swap(arr,i,min);
  }
}
//NOPP-BEGIN
/*
Local Variables:
compile-command: "frama-c -jessie sort_array.c"
End:
*/
//NOPP-END
