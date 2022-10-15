/* FUNCTION CONTRACTS */

int A, B, C, M;

/*@ ensures M >= x && M >= y;
    ensures M == x || M == y;
*/

void max (int x, int y)
{
  M = (x > y) ? x : y;
}





















#include "../share/builtin.h"


void main(void)
{
  A = Frama_C_interval(0,100);
  B = Frama_C_interval(200,300);
  max(A, B);
  //@ assert M >= A && M >= B ;
}




/*
Local Variables:
compile-command: "toplevel.opt 1max.c"
End:
*/
