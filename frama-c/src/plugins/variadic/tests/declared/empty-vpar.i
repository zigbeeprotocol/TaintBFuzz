/*@ behavior bhv:
  @ requires c>0;
  @ requires a<=42;
*/
void f(const int a, int, int c,...);

int main(){
  f(1, 2, 3);
  return 0;
}
