#include <stdarg.h>

int max(int n, ...){
  int i, val, ret;

  va_list list;
  va_start(list, n);
  ret = va_arg(list, int);

  for(i=1; i<n; i++){
    val = va_arg(list, int);
    ret = ret > val ? ret : val;
  }

  va_end(list);
  return ret;
}

int main(){
  return max(6, 3, -7, 14, 42, 23, -57, 73, 92, 8); // Too many vargs
}

