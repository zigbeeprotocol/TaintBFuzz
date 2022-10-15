#include <string.h>

typedef unsigned t;
struct X { t  s_addr; };

void test() {
  struct X x;
  memset(&x, 0, sizeof(x));
}
