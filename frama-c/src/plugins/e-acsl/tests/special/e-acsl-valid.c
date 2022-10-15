/* run.config
   COMMENT: test option -e-acsl-no-valid
   STDOPT: #"@GLOBAL@ -eva -eva-verbose 0 -then -no-eva -e-acsl-no-valid"
*/
/* run.config_dev
   MACRO: ROOT_EACSL_GCC_FC_EXTRA_EXT -eva -eva-verbose 0
   MACRO: ROOT_EACSL_GCC_OPTS_EXT --then --e-acsl-extra -e-acsl-no-valid
*/

#include <stdlib.h>

/*@ requires \valid(y);
  @ requires *x >= 0;
  @ ensures *x == \old(*x)+1;
  @ assigns *x \from *x,x;
  @ behavior b1:
  @   assumes *x == 1;
  @   assigns \nothing;
  @   ensures *x < 0;
  @ behavior b2:
  @   assumes *x == 0;
  @   ensures *x == 1;
  @ complete behaviors;
  @ disjoint behaviors b1, b2;
  @ */
void f(int *x, int *y) {
  /*@ requires *x >= 0;
    @ ensures 2 >= 1;
    @ assigns *x; */
  { (*x)++; }
  /*@ loop invariant 0 <= i <= 1;
    @ loop variant 2 - i; */
  for (int i = 0; i < 1; i++) /*@ assert 1 == 1; */ /*@ assert \valid(y); */
    ;
}

int main(void) {
  int x = 0;
  int *y = (int *)malloc(sizeof(int));
  f(&x, y);
  return 0;
}
