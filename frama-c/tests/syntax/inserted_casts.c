/* run.config
   MODULE: @PTEST_NAME@
   STDOPT: +"-no-autoload-plugins"
   STDOPT: +"-no-autoload-plugins" +"-machdep x86_64"
*/
#include "stddef.h"
int f(int b)
{
    int r;
	if (b*b != 0)
        r=0;
	else r=-1;
    return r;
}

int g(int a)
{
  unsigned int r;
  ptrdiff_t x = &r - &r;
  r = a + 3;
  a *= r;
  return (a - r);
}
