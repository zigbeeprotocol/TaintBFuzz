/* run.config
STDOPT: +"-eva-no-alloc-returns-null"
*/


#include <stdlib.h>
#include <stdarg.h>

int *pack(int first, ...){
  int *ret;
  int size, i;
  va_list list;

  va_start(list, first);
  size = 1;
  while (va_arg(list, int))
    size++;
  va_end(list);

  ret = malloc(sizeof(int) * (size + 1));
  ret[0] = first;
  va_start(list, first);
  for(i = 0; i<size; i++){
    ret[i+1] = va_arg(list, int);
  }
  va_end(list);

  return ret;
}

int main(){
  int *p = pack(42, 42, 42, 42, 42, 42, 0);
  return p[0];
}

