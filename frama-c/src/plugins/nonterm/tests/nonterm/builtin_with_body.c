/* run.config
   STDOPT: #"-eva-builtin memcpy:Frama_C_memcpy -eva-warn-key=builtins:override=inactive"
 */

#include <string.h>

void *memcpy(void *dest, const void *src, size_t n) {
  return NULL;
}

int main() {
  int a, b = 2;
  memcpy(&a, &b, sizeof(int));
  return 0;
}
