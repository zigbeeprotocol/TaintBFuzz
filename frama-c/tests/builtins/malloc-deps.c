/* run.config*
   OPT: -eva @EVA_CONFIG@ -deps -calldeps -inout -eva-slevel 5 -eva-msg-key malloc
*/
#include <stdlib.h>

volatile int v;
void g(int *p, int k) { p[k] = k; }

void main(int i, int j) {
  int *p, *q;
  /*@ eva_allocate fresh_weak; */
  p = malloc(100);
  *p = i;
  *p = j; // Cannnot perform strong update for deps, variable is weak

  /*@ eva_allocate fresh; */
  q = malloc(100);
  *q = i;
  *q = j; // Can perform strong update for deps


  int *r;
  for (int l=0; l<10; l++) {
    /*@ eva_allocate by_stack; */
    r = malloc((l+1)*4);
    g(r, l+v); // Again, we can only perform weak updates (after iteration 1)
  }
}
