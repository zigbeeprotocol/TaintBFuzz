#include <stdarg.h>

int sum(int n, ...){
  int ret = n;
  int tmp;
  va_list list;
  va_start(list, n);

  do
  {
    tmp = va_arg(list, int);
    ret += tmp;
  }
  while (tmp);

  va_end(list);
  return ret;
}

int main(){
  return sum(6, 9, 14, 12, 1, 0); // The params must be terminated by 0
}

