void f(int *p) {
  *p = 0;
}

void g(int *p) {
  *p = 1;
}

int main(void) {
  int t[3];
  f(&t[0]);
  /*@ assert \initialized(&t[0]); */
  t[1] = 1;
  g(&t[1]);
  g(&t[2]);
  /*@ assert \initialized(&t[1]); */
  /*@ assert \initialized(&t[2]); */
  return 0;
}
