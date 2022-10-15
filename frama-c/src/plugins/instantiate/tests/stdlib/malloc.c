#include <stdlib.h>

struct X {
  int x ;
  int y ;
} ;

struct Flex {
  int x ;
  char c ;
  int f[] ;
} ;

struct incomplete ;

int main(void){
  int* pi = malloc(sizeof(int) * 10) ;
  float* pf = malloc(sizeof(float) * 10) ;
  struct X* px = malloc(sizeof(struct X) * 10) ;
  char* pc = malloc(10) ;
  int (*pa) [10] = malloc(sizeof(int[10]) * 10) ;
  struct Flex* f = malloc(sizeof(struct Flex) + 3 * sizeof(int)) ;
  void *v = malloc(sizeof(char) * 10);
  struct incomplete* inc = malloc(10);
}
