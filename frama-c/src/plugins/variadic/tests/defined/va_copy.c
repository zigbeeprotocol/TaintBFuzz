/* run.config
STDOPT: +"-eva-no-alloc-returns-null"
*/


#include <stdlib.h>
#include <stdarg.h>

int *pack(int first, ...){
  int *ret;
  int size, i;
  va_list list, list_count;
  va_start(list, first);

  va_copy(list_count, list);
  size = 1;
  while (va_arg(list_count, int))
    size++;
  va_end(list_count);

  ret = malloc(sizeof(int) * (size + 1));
  ret[0] = first;
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

