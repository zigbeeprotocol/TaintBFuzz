#include <string.h>

struct X {
  int x ;
  int y ;
} ;

typedef int named ;

int integer(int s1[10], int s2[10]){
  return memcmp(s1, s2, 10 * sizeof(int));
}

int with_named(named s1[10], named s2[10]){
  return memcmp(s1, s2, 10 * sizeof(named));
}

int structure(struct X s1[10], struct X s2[10]){
  return memcmp(s1, s2, 10 * sizeof(struct X));
}

int pointers(int* s1[10], int* s2[10]){
  return memcmp(s1, s2, 10 * sizeof(int*));
}

int nested(int (*s1)[10], int (*s2)[10], int n){
  return memcmp(s1, s2, n * sizeof(int[10]));
}

int with_void(void *s1, void *s2, int n){
  return memcmp(s1, s2, 10) ;
}

struct incomplete ;
int with_incomplete(struct incomplete* s1, struct incomplete* s2, int n){
  return memcmp(s1, s2, n);
}

void with_null_or_int(int p[10]){
  memcmp(NULL, p, 10 * sizeof(int));
  memcmp(p, NULL, 10 * sizeof(int));
  memcmp((int const*)42, p, 10 * sizeof(int));
  memcmp(p, (int const*)42, 10 * sizeof(int));
}
