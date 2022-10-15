#include <string.h>

union U {
  int x ;
  unsigned y ;
};
struct X { union U u ; };
void test() {
  struct X x;
  memset(&x, 0, sizeof(x));
}
