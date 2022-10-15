/* run.config
   STDOPT:
   STDOPT: +"-machdep gcc_x86_32"
   STDOPT: +"-machdep msvc_x86_64"
 */

#include <stdarg.h>

struct st {
  char a;
  int b;
};

void fva(int a, ...) {
  va_list ap;
  __builtin_va_start(ap, a); // Non-MSVC-specific
  __builtin_va_end(ap); // Non-MSVC-specific
}

int main() {
  int x = 0;
  if (__builtin_expect(x++, x)) { // GCC-specific
    int y = x;
  }
  __builtin__annotation("a", 1); // MSVC-specific
  fva(1);
  __builtin_offsetof(struct st,b); // Generic builtin (always available)
}
