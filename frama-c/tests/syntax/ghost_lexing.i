int G = 0;

/*@ ghost int H = 1; */

const char* foo = "foo";

void test(const char */*name*/);

void test2(int x) {
  /*@ ghost
    int y = 0;
    if (x>0) { y = x * x; };
  */
  G = x * x;
  test(foo);
}

void f() {
  /*@ ghost L:; */ G++;
  /*@ assert \at(G,L) + 1 == G; */
  L1: /*@ ghost H=G; */ G++;
  if (G < 30) goto L1;
  /*@ assert H == \at(G,L1); */
}
