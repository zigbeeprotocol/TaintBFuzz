/* run.config
   STDOPT: #" -warn-special-float non-finite -print -machdep x86_32"
*/
#define _ISOC99_SOURCE
#include <math.h>

void main() {
  double d = 0x1p10000;
  d = 0.;
  double e = (d/d) + d;
}
