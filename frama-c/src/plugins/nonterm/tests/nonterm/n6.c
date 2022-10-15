/* run.config
   STDOPT: #"-eva-builtin memcpy:Frama_C_memcpy"
 */

#include <string.h>

int main() {
  int a, b = 2;
  memcpy(&a, &b, sizeof(int));
  return 0;
}
