/* run.config*
   OPT: -eva @EVA_CONFIG@ -eva-slevel 10 -eva-mlevel 0 -eva-alloc-builtin by_stack
*/
#include <stdlib.h>

void main(int c) {
  int x;
  int *s;
  if(c) {
    x = 1;
    s = malloc(100);
  } else {
    x = 2;
    s = 0;
  }

  int *p = malloc(c);
  int *q = malloc(12);
  /*@ eva_allocate fresh; */
  int *r = malloc(100);
  *p = 1;
  *(p+2) = 3;
  *(p+24999) = 4;

  *q = 1;
  Frama_C_show_each(q+2);
  *(q+2) = 3;

  *r = 1;
  *(r+2) = 3;

  /*@ eva_allocate imprecise; */
  int *mw = malloc(42);
  *mw = 1;
  /*@ eva_allocate imprecise; */
  int *mw2 = malloc(42);
  *mw2 = 2;

  //  *s = 1;
}
