/* run.config*
   STDOPT: #"-eva-slevel 10 -big-ints-hex 257"
   STDOPT: #"-eva-slevel 10 -big-ints-hex 257" +"-machdep ppc_32"
*/

#include <math.h>

void main() {
  int k;
  double i = -(double)0;
  double j = sqrt (i);
  //@ assert i == j;

  //@ assert sizeof(long long) == sizeof(double);
  long long r;
  unsigned long long *p = &j;
  unsigned int c[8];

  Frama_C_dump_each();

  r = *p;

  Frama_C_dump_each();

  Frama_C_show_each_long_long(r);
  Frama_C_show_each_double(j);

  for (k=0; k<8; k++)
    c[k] = ((unsigned char*)&i)[k];

}
