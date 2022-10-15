#include <stdarg.h>

float vsum(int n, va_list list){
  int i;
  float ret = 0.0;
  for(i = 0; i<n; i++){
    if (va_arg(list, int))
      ret += va_arg(list, double);
    else
      ret += va_arg(list, int);
  }
  return ret;
}

float sum(int n, ...){
  int tmp;
  va_list list;
  va_start(list, n);
  tmp = vsum(n, list);
  va_end(list);
  return tmp;
}

int main(){
  return sum(4, 1, 3.5, 0, 14, 1, 3.5, 0, 21);
}

