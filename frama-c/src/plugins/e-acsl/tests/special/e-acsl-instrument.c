/* run.config
   COMMENT: test option -e-acsl-instrument; cannot run Eva on this example
   STDOPT:#"-e-acsl-instrument='@all,-uninstrument1,-uninstrument2'"
*/
/* run.config_dev
   MACRO: ROOT_EACSL_GCC_OPTS_EXT --no-assert-print-data
   MACRO: ROOT_EACSL_GCC_FC_EXTRA_EXT -e-acsl-instrument @all,-uninstrument1,-uninstrument2
*/

#include <stdarg.h>

int uninstrument1(int *p) {
  *p = 0;
  return 0;
}

/*@ requires \valid(p); */
int uninstrument2(int *p) {
  {
    int *q = p;
    *p = 0;
    goto L;
  }
L:
  return 0;
}

int instrument1(int *p) {
  *p = 0;
  return 0;
}

/*@ requires \valid(p); */
int instrument2(int *p) {
  {
    int *q = p;
    *p = 0;
    goto L;
  }
L:
  return 0;
}

/* test combination of -e-acsl-instrument and -variadic-no-translation;
   see gitlab's issue #88 */
int vol(int n, ...) {
  va_list vl;
  va_start(vl, n);
  int r = va_arg(vl, int);
  va_end(vl);
  return 0;
}

int main(void) {
  int x;
  int y = 0;
  instrument1(&x);
  uninstrument1(&x);
  instrument2(&x);
  uninstrument2(&x);
  /*@ assert \initialized(&x); */
  /*@ assert \initialized(&y); */
  return vol(6, 1);
}
