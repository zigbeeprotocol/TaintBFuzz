/*run.config
  STDOPT: #"-c11"
*/

#include <stdnoreturn.h>

noreturn void f(void) {
  while (1);
}

_Noreturn void g(void) {
  while (2);
}

volatile int v;

int main() {
  if (v) f();
  if (v) g();
}
