#include <stddef.h>

void* malloc(size_t s);
void* calloc(size_t num, size_t size);
void free(void* ptr);

void foo(void){
  int * p = malloc(sizeof(int));
  int * q = calloc(2, sizeof(int));
  free(p);
  free(q);
}
