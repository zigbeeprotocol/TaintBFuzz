/*@ behavior bhv1:
  @ requires c>0;
  @ requires a<=42;
  @ ensures \result > 0;
*/
int f(const int a, int, int c,...);

int call1(){
  return f(1, 2, 3, 4, 5, 6);
}

/*@ behavior bhv2:
  @ requires b<=0;
*/
void g(int b, int c, ...);

void call2(){
  g(-2, 3, 4);
}

int main(){
  call2();
  return call1();
}
