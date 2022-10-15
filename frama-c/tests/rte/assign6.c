/* run.config
   STDOPT: #" -warn-signed-overflow -print"
*/

int z;

/*@
 assigns z \from y;
 assigns \result \from x,y;
*/
int f(int x, int y);

int main() {
  int a,b;
  a = f(0,0);
  a = f(0,b);
  a = f(b,0);
  return a;
}
