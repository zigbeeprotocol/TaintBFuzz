#include "stdlib.h"

extern void *malloc(size_t);
extern void free(void*);

int f(void) {
  int *x;
  x = (int*)malloc(sizeof(int));
  /*@ assert \valid(x); */
  free(x);
  /*@ assert freed: \valid(x); */
  return 0;
}
