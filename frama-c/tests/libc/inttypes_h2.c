#include <inttypes.h>

volatile int nondet;

void main() {
  intmax_t a, b;
  imaxdiv_t r;
  if (nondet) {
    a = INTMAX_MIN;
    b = -1;
    r = imaxdiv(a, b);
    //@ assert unreachable: \false;
  }
  if (nondet) {
    a = INTMAX_MAX;
    b = 0;
    r = imaxdiv(a, b);
    //@ assert unreachable: \false;
  }
  a = INTMAX_MAX;
  b = INTMAX_MAX/2; // note: division rounds down
  r = imaxdiv(a, b);
  //@ assert r.quot == 2;
  //@ assert r.rem == 1;

  a = imaxabs(INTMAX_MAX);
  //@ assert a == INTMAX_MAX;
  a = imaxabs(INTMAX_MIN + 1);
  //@ assert a >= 0;
  a = imaxabs(0);
  //@ assert a == 0;
}
