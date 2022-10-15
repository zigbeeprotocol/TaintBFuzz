/* run.config
   PLUGIN:
   OPT: -constfold -print -machdep x86_32
*/
#include <stddef.h>

typedef const size_t const_size_t;

static const_size_t c1 = 300;
static const size_t c2[2] = { 5, c1 + 1 + c1 };
static const size_t c3[3][2][4] =
{ [0][0][0] = c2[0],
  [0][1][2] = c2[1] + 1 + c1,
  [1][1][3] = c1 + 2 };

size_t f (size_t y)
{
  /*@ assert c1 == 300; */
  size_t tmp2 = (c3[0][2-2][0+0] * y - c2[1] / c3[1-1][1][2] + c2[2-1]);
  return tmp2;
}
