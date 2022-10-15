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
