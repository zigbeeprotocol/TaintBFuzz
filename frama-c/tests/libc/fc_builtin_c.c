#include "__fc_builtin.c"
#include <limits.h>

// The "sampling:unknown" assertions check whether a given value _may_ be
// in the interval; they are supposed to return 'unknown', but never 'invalid'.

int main() {
  int i = Frama_C_interval(10, INT_MAX - 20);
  //@ assert bounds: 10 <= i <= INT_MAX - 20;
  //@ assert sampling:unknown: i == INT_MAX/2;

  char c = Frama_C_char_interval(CHAR_MIN + 1, CHAR_MAX - 4);
  //@ assert bounds: CHAR_MIN + 1 <= c <= CHAR_MAX - 4;
  //@ assert sampling:unknown: c == 42;

  unsigned int ui = Frama_C_unsigned_int_interval(INT_MAX, UINT_MAX);
  //@ assert bounds: INT_MAX <= ui <= UINT_MAX;
  //@ assert sampling:unknown: ui == UINT_MAX - 10000;

  float f = Frama_C_float_interval(1.0, 2.0);
  //@ assert bounds: 1.0 <= f <= 2.0;
  //@ assert sampling:unknown: f == 1.5;

  double one_e_100 = 0x1.249ad2594c37dp332;
  double d = Frama_C_double_interval(1e10, one_e_100);
  //@ assert bounds: 1e10 <= d <= one_e_100;
  //@ assert sampling:unknown: d == 12345678901.2;

  long l = Frama_C_long_interval(LONG_MIN, -2L);
  //@ assert bounds: LONG_MIN <= l <= -2;
  //@ assert sampling:unknown: l == -3;

  unsigned long ul =
    Frama_C_unsigned_long_interval(LONG_MAX - 1UL, LONG_MAX + 1UL);
  //@ assert bounds: LONG_MAX - 1 <= ul <= LONG_MAX + 1;
  //@ assert sampling:unknown: ul == LONG_MAX;
}
