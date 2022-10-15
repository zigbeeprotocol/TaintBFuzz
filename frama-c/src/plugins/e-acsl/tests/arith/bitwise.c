/* run.config
   COMMENT: Support of bitwise operations
   STDOPT: #"-warn-right-shift-negative -warn-left-shift-negative"
*/
/* run.config_dev
   MACRO: ROOT_EACSL_GCC_FC_EXTRA_EXT -warn-right-shift-negative -warn-left-shift-negative
*/

#include <limits.h>

// Operations on signed C integers
void f_signed(int a, int b) {
  int c = a << 2;
  /*@ assert c == (a<<2); */
  int d = b >> 2;
  /*@ assert d == (b>>2); */
  int e = a | b;
  /*@ assert e == (a | b); */
  int f = a & b;
  /*@ assert f == (a & b); */
  int g = a ^ b;
  /*@ assert g == (a ^ b); */
}

// Operations on unsigned C integers
void f_unsigned(unsigned int a, unsigned int b) {
  unsigned int c = a << 2u;
  /*@ assert c == (a<<2); */
  unsigned int d = b >> 2u;
  /*@ assert d == (b>>2); */
  unsigned int e = a | b;
  /*@ assert e == (a | b); */
  unsigned int f = a & b;
  /*@ assert f == (a & b); */
  unsigned int g = a ^ b;
  /*@ assert g == (a ^ b); */
}

// Operations on arbitrary precision signed integers
void g_signed(int a, int b) {
  int c = a << b;
  /*@ assert c == (a<<b); */
  int d = a >> b;
  /*@ assert d == (a>>b); */

  /*@ assert ((ULLONG_MAX + 1) << 1) != 0; */
  /*@ assert ((ULLONG_MAX + 1) >> 1) != 0; */
  /*@ assert (1 << 65) != 0; */
  /*@ assert ((ULLONG_MAX + 1) | (LLONG_MIN - 1)) != 0; */
  /*@ assert ((ULLONG_MAX + 1) & (LLONG_MIN - 1)) !=
               ((ULLONG_MAX + 1) ^ (LLONG_MIN - 1)); */
}

// Operations on arbitrary precision unsigned integers
void g_unsigned(unsigned int a, unsigned int b) {
  unsigned int c = a << b;
  /*@ assert c == (a<<b); */
  unsigned int d = a >> b;
  /*@ assert d == (a>>b); */

  /*@ assert ((ULLONG_MAX + 1u) << 1u) != 0; */
  /*@ assert ((ULLONG_MAX + 1u) >> 1u) != 0; */
  /*@ assert (1u << 65u) != 0; */
  /*@ assert ((ULLONG_MAX + 1u) | 1u) != 0; */
  /*@ assert ((ULLONG_MAX + 1u) & 1u) !=
               ((ULLONG_MAX + 1u) ^ 1u); */
}

int main() {
  int a = 4;
  int b = 8;
  f_signed(a, b);
  f_unsigned(a, b);
  g_signed(a, b);
  g_unsigned(a, b);
  return 0;
}
