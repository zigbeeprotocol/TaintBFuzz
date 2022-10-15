#include <stdarg.h>

int sum(int n, ...){
  int ret = 0;
  int i;
  va_list list;
  va_start(list, n);
  for(i=0; i<n; i++){
    ret += va_arg(list, short); // Impossible to get a short here
  }

  va_end(list);
  return ret;
}

int main(){
  short x = 1, y = 2, z = 3;
  return sum(3, x, y, z); // x, y and z should be promoted to int
}

