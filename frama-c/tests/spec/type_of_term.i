/* run.config
 MODULE: Type_of_term
   STDOPT:
*/

int t [42];

struct S { int x; int y[]; } s;

/*@ assigns *(p+(..)), t[..], s[..].x, s[..].y[..]; 
*/
void f(int *p, struct S* s);

int main() {
  f(t,&s);
  return 0;
}
