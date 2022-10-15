/* REQUIRE CLAUSES */

int A, B, C, M;


/*@
  requires \valid(p) && \valid(q);
  ensures M >= *p && M >= *q;
  ensures M == *p || M == *q;
*/
void max (int *p, int *q) 
{ 
  M = (*p > *q) ? *p : *q;
}














#include "../share/builtin.h"


void main(void)
{
  A = Frama_C_interval(0,100);
  B = Frama_C_interval(50,300);
  max(&A, &B);
  //@ assert M >= A && M >= B ;
  C = 250;
  max(&A, Frama_C_nondet_ptr(&B, &C));
  //@ assert M == A || M == B || M == C ;
}
