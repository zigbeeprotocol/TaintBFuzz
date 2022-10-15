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

enum E { A, B, C };

int main(void){
  int* pi = calloc(10, sizeof(int)) ;
  enum E* pe = calloc(10, sizeof(enum E)) ;
  float* pf = calloc(10, sizeof(float)) ;
  struct X* px = calloc(10, sizeof(struct X)) ;
  char* pc = calloc(10, sizeof(char)) ;
  int (*pa) [10] = calloc(10, sizeof(int[10])) ;
  struct Flex* f = calloc(1, sizeof(struct Flex) + 3 * sizeof(int)) ;
  void *v = calloc(10, sizeof(char));
  struct incomplete* inc = calloc(10, 10);
}
