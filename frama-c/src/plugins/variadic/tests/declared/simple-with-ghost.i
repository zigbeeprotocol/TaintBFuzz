/*@ behavior bhv:
  @ requires c>0;
  @ requires a<=42;
  @ ensures \result > 0;
*/
int f(const int a, int, int c,...) /*@ ghost (int x) */;

int main(){
  return f(1, 2, 3, 4, 5, 6) /*@ ghost(7) */;
}
