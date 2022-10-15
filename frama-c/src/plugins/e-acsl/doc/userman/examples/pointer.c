#include <stdlib.h>

extern void *malloc(size_t);
extern void free(void*);

int main(void) {
  int *x;
  x = (int*)malloc(sizeof(int));
  *x = 1;
  /*@ assert *x == 1; */
  free(x);
  /*@ assert freed: *x == 1; */
  return 0;
}
