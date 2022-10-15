/* COMPLETE vs PARTIAL specification */

int A, B, C, M;

/*@ ensures M >= x && M >= y;
    ensures M == x || M == y;
*/
void max (int x, int y) 
{ 
  M = (x > y) ? x : y;
}

/*
If we wrote a critical function Critical that relied 
on the max function above, would we be ready to drop in
its place any third-party function, provided that this
function is proved to satisfy the specification? 
*/

void Critical(void)
{
/* compute in M the max of A, B, and C, 
or else THE PLANE WILL CRASH!!! */
   max(B, C);
   max(M, A);
}






void max(int x, int y)
{
  while (1);
}

void max (int x, int y) 
{
  A = -x;
  B = -y;
  M = (A < B) ? x : y;
}
/*
In real life, specifications are almost always partial,
but still useful.

This is a question that can be answered by writing
the specification of Critical and by proving that 
this specification is satisfied assuming only that
max satisfies its own specification 
(not using any specific implementation) */

