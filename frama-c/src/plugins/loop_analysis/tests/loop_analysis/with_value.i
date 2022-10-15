/*run.config
PLUGIN: @PTEST_PLUGIN@ from,inout,eva,scope
OPT: -eva -eva-show-progress -then -loop
*/
void f1(int n) {
  for (int i = 1; i < n+2; i++); // i IN [1..6] (6)
}

void f2(int n) {
  for (int i = 1; i <= n+2; i++); // i IN [1..7] (7)
}

void f3(int n) {
  for (int i = 1; n+2 >= i; i++); // i IN [1..7] (7)
}

void f4(int n) {
  for (int i = 1; n+2 > i; i++); // i IN [1..6] (6)
}

void f5(int n) {
  for (int i = n+2; 3 < i; i--); // i IN [4..7] (4)
}

void f6(int n) {
  for (int i = n+2; 3 <= i; i--); // i IN [3..7] (5)
}

void f7(int n) {
  for (int i = n+2; i >= 3; i--); // i IN [3..7] (5)
}

void f8(int n) {
  for (int i = n+2; i > 3; i--); // i IN [4..7] (4)
}

void g1(int n) {
  for (int i = 1; i < n+2; i++); // i IN BOT
}

void g2(int n) {
  for (int i = 1; i <= n+2; i++); // i IN BOT
}

void g3(int n) {
  for (int i = 1; n+2 >= i; i++); // i IN BOT
}

void g4(int n) {
  for (int i = 1; n+2 > i; i++); // i IN BOT
}

void g5(int n) {
  for (int i = n+2; 1 < i; i--); // i IN BOT
}

void g6(int n) {
  for (int i = n+2; 1 <= i; i--); // i IN BOT
}

void g7(int n) {
  for (int i = n+2; i >= 1; i--); // i IN BOT
}

void g8(int n) {
  for (int i = n+2; i > 1; i--); // i IN BOT
}

void h1(int n) {
  for (int i = 1; i < n+2; i++); // i IN [1..21] (21)
}

void h2(int n) {
  for (int i = 1; i <= n+2; i++); // i IN [1..22] (22)
}

void h3(int n) {
  for (int i = 1; n+2 >= i; i++); // i IN [1..22] (22)
}

void h4(int n) {
  for (int i = 1; n+2 > i; i++); // i IN [1..21] (21)
}

void h5(int n) {
  for (int i = n+2; 1 < i; i--); // i IN [2..22] (21)
}

void h6(int n) {
  for (int i = n+2; 1 <= i; i--); // i IN [1..22] (22)
}

void h7(int n) {
  for (int i = n+2; i >= 1; i--); // i IN [1..22] (22)
}

void h8(int n) {
  for (int i = n+2; i > 1; i--); // i IN [2..22] (21)
}

void i1(int n1, int n2) {
  for (int i = n1-2; i < n2+3; i++); // i IN [2..14] (13)
}

void i2(int n1, int n2) {
  for (int i = n1-2; i <= n2+3; i++); // i IN [2..15] (14)
}

void i3(int n1, int n2) {
  for (int i = n2-2; i > n1+3; i--); // i IN [8..10] (3)
}

void i4(int n1, int n2) {
  for (int i = n2-2; i >= n1+3; i--); // i IN [7..10] (4)
}

void j1(int n1, int n2) {
  for (int i = n1-4; i < n2+7; i++); // i IN [6..46] (41)
}

void j2(int n1, int n2) {
  for (int i = n1-4; i <= n2+7; i++); // i IN [6..47] (42)
}

void j3(int n1, int n2) {
  for (int i = n2-4; i > n1+7; i--); // i IN [18..36] (19)
}

void j4(int n1, int n2) {
  for (int i = n2-4; i >= n1+7; i--); // i IN [17..36] (20)
}

void f2_u_const() {
  for (unsigned i = 1; i <= 7; i++); // i IN [1..7] (7)
}

void ne1() {
  for (int i = 3; i + 4 != 50; i++); // i IN [3..45] (43)
}

void ne2() {
  for (int i = -100; i + 4 != 50; i++); // i IN [-100..45] (146)
}

void ne3() {
  for (int i = 100; i + 4 != 50; i--); // i IN [55..100] (46)
}

void ne4() {
  for (int i = -100; i + 4 != -150; i--); // i IN [-145..-100] (46)
}

void nev1(int a, int b) {
  for (int i = a; i + 4 != b; i++); // i IN [3..45] (43)
}

void nev2(int a, int b) {
  for (int i = a; i + 4 != b; i++); // i IN [-100..45] (146)
}

void nev3(int a, int b) {
  for (int i = a; i + 4 != b; i--); // i IN [55..100] (46)
}

void nev4(int a, int b) {
  for (int i = a; i + 4 != b; i--); // i IN [-145..-100] (46)
}

void nev5(int a, int b) {
  for (int i = a; b != i + 4; i++); // i IN [3..45] (43)
}

void nev6(int a, int b) {
  for (int i = a; b != i + 4; i++); // i IN [-100..45] (146)
}

void nev7(int a, int b) {
  for (int i = a; b != i + 4; i--); // i IN [55..100] (46)
}

void nev8(int a, int b) {
  for (int i = a; b != i + 4; i--); // i IN [-145..-100] (46)
}

volatile int nondet;
int main() {
  f1(5);
  f2(5);
  f3(5);
  f4(5);
  f5(5);
  f6(5);
  f7(5);
  f8(5);
  g1(nondet);
  g2(nondet);
  g3(nondet);
  g4(nondet);
  g5(nondet);
  g6(nondet);
  g7(nondet);
  g8(nondet);
  h1(10);
  h1(20);
  h2(10);
  h2(20);
  h3(10);
  h3(20);
  h4(10);
  h4(20);
  h5(10);
  h5(20);
  h6(10);
  h6(20);
  h7(10);
  h7(20);
  h8(10);
  h8(20);
  i1(4, 12);
  i2(4, 12);
  i3(4, 12);
  i4(4, 12);
  j1(20, 30);
  j2(20, 30);
  j3(20, 30);
  j4(20, 30);
  j1(10, 40);
  j2(10, 40);
  j3(10, 40);
  j4(10, 40);

  f2_u_const();

  ne1();
  ne2();
  ne3();
  ne4();
  nev1(3, 50);
  nev2(-100, 50);
  nev3(100, 50);
  nev4(-100, -150);
  nev5(3, 50);
  nev6(-100, 50);
  nev7(100, 50);
  nev8(-100, -150);
  return 0;
}
