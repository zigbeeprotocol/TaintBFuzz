/*@ behavior bhv:
  @ requires c>0;
  @ requires a<=42;
*/
void f(const int a, int, int c,...) /*@ ghost(int x) */;

int main(){
  f(1, 2, 3) /*@ ghost(4) */;
  return 0;
}
