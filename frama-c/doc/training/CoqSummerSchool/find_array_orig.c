//NOPP-BEGIN
/*@ lemma div_def: \forall integer i; 0<= i - 2*(i/2) <= 1; */

/*@
  predicate sorted{L}(int* arr, integer length) =
  \forall integer i,j; 0<=i<=j<length ==> arr[i] <= arr[j];
*/
//NOPP-END

int find_array(int* arr, int length, int query) {
  int low = 0;
  int high = length - 1;
  while (low <= high) {
    int mean = low + (high -low) / 2;
    if (arr[mean] == query) return mean;
    if (arr[mean] < query) low = mean + 1;
    else high = mean - 1;
  }
  return -1;
}

//NOPP-BEGIN
/*
Local Variables:
compile-command: "frama-c -jessie find_array.c"
End:
*/
//NOPP-END
