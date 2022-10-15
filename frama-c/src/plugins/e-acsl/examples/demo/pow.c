#include "stdio.h"

int pow(int x, unsigned int n) {
  unsigned int res = 1;
  while (n) {
    if (n & 1) res *= x;
    n >>= 1;
    x *= x;
  }
  return res;
}
