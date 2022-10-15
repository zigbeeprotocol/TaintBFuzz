#include <stdint.h>
void main () {
  char c;
  uintptr_t a = &c;
  char *p = (char *) (a + 1);
  char *q = (char *) (a + 2);
}
