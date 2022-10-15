void insert(int* arr, int length, int val);

void insert_sort(int* arr, int length);

void insert(int* arr, int length, int val) {
  int i = length -1;
  while(i>=0 && arr[i] > val) { arr[i+1] = arr[i]; i--; }
  arr[i+1] = val;
  return;
}

void insert_sort(int* arr, int length)  {
  for(int i = 1; i < length; i++) { insert(arr,i,arr[i]); }
}

//NOPP-BEGIN
/*
Local Variables:
compile-command: "frama-c -jessie insert_sort.c"
End:
*/
//NOPP-END
