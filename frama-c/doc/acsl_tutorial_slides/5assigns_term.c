int A, B, C, M;

/* this is probably the complete specification 
   that we expect for max: */

requires p == &a || p == &b
/*@ ensures M >= x && M >= y;
    ensures M == x || M == y;
    terminates true; // implicit
    assigns a,b;
*/
void max (int x, int y) 
{
  *p = ..
/*
Any implementation that satisfies this specification
ought to keep the plane in the air */
