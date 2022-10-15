#include <string.h>

struct X {
  int x ;
  int y ;
} ;

typedef int named ;

void integer(int src[10], int dest[10]){
  int * res = memcpy(dest, src, 10 * sizeof(int));
  memcpy(src, res, 10 * sizeof(int));
}

void with_named(named src[10], named dest[10]){
  named * res = memcpy(dest, src, 10 * sizeof(named));
  memcpy(src, res, 10 * sizeof(named));
}

void structure(struct X src[10], struct X dest[10]){
  struct X * res = memcpy(dest, src, 10 * sizeof(struct X));
  memcpy(src, res, 10 * sizeof(struct X));
}

void pointers(int* src[10], int* dest[10]){
  int ** res = memcpy(dest, src, 10 * sizeof(int*));
  memcpy(src, res, 10 * sizeof(int*));
}

void nested(int (*src)[10], int (*dest)[10], int n){
  int (*res) [10] = memcpy(dest, src, n * sizeof(int[10]));
  memcpy(src, res, n * sizeof(int[10]));
}

void with_void(void *src, void *dest, int n){
  void *res = memcpy(dest, src, n);
  memcpy(src, res, n);
}

struct incomplete ;
void with_incomplete(struct incomplete* src, struct incomplete* dest, int n){
  struct incomplete* res = memcpy(dest, src, n);
  memcpy(src, res, n);
}

void with_null_or_int(int p[10]){
  memcpy(NULL, p, 10 * sizeof(int));
  memcpy(p, NULL, 10 * sizeof(int));
  memcpy((int*)42, p, 10 * sizeof(int));
  memcpy(p, (int*)42, 10 * sizeof(int));
}
