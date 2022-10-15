/*@ assigns \result \from i; */
int factorial (int i) {
  if(i <= 1) return 1;
  return i * factorial (i - 1);
}

void main(void) {
  int x = factorial(8);
  int y = factorial(20);
}
