#include <stdarg.h>

/*@ requires n>= 0; */
int sum(int n, ...){
  int ret = 0;
  int i = 0;
  va_list list;
  va_start(list, n);

  /*@ loop invariant 0<=i; */
  for(i=0; i<n; i++){
    ret += va_arg(list, int);
  }

  va_end(list);
  return ret;
}

int main(){
  return sum(5, 6, 9, 14, 12, 1);
}
