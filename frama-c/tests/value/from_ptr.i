/* run.config*
   
   STDOPT: #"-main main"
   STDOPT: #"-main main1"
*/
long i,j,x,k,l,m,n,d,a,b;

int p[10][10][10]={0};
long *q;

void main(int c) {
  i = (long) &p[11];
  i = (long) &p[10];

  if (c)
    // This branch is assumed to be dead since "i" is an invalid pointer.
    *((int*)i) = a;

  q = c ? &a : &b ; // So, "q" points only on "b".
  d = *q; // "d" is only from "a" and "c".
}

void main1(int c) {
  i = (long) &p[1];
  i = (long) &p[0];

  if (c) *((int*)i) = a;

  q = c ? &a : &b ;
  d = *q;
}
