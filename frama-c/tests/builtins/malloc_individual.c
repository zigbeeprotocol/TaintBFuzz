/* run.config*
   STDOPT: #"-eva-alloc-builtin fresh"
*/

#include "stdlib.c"

int *p;
int A,B,C;

void main(int c)
{
  p = malloc(sizeof(int));
  if (c)
    *p = 3;
  A = *p;
  C = 1 + *p;
  B = A;
}
