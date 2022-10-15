/* run.config*
   OPT: -eva @EVA_CONFIG@ -eva-memexec -deps -inout -eva-mlevel 0
*/
#include <stdlib.h>

void f(int *p, int i) {
  *p = i;
}

volatile v;

void main() {
  /*@ eva_allocate fresh; */
  int *p = malloc (4);
  if (v) {
    f(p, 2);
    f(p, 1); // This call or the corresponding one below could be cached. It is not, because we forbid memexec to take full updates to a strong variable into account for malloced bases, because they may become weak later
  } else {
    f(p, 1);
  }

  /*@ eva_allocate fresh_weak; */
  int *q = malloc (4);
  if (v) {
    f(q, 2);
    f(q, 1);
  } else {
    f(q, 1); // This call cannot be cached; since q is weak, f(q, i)
             // actually depends on *q
  }
}
