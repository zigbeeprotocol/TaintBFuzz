/* run.config*
   STDOPT: +"-eva-alloc-builtin imprecise"
*/

#include <stdlib.h>

volatile int v;

void main() {
  int *p = malloc(sizeof(int));
  *p = 17;
  int *pp = p;
  int *q = realloc(p, 2 * sizeof(int));
  if (v) {
    int *r = realloc(q, sizeof(int));
    free(r);
  }
}
