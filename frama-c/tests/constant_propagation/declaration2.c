/* run.config
   OPT: -eva @EVA_OPTIONS@ -then -scf
*/

void f(int *x) { (*x)++; }

int main () {
  int Y = 42;
  f(&Y);
  return Y;
}
