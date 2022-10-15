/* run.config
DONTRUN: main test is at @PTEST_DIR@/inconsistent_decl.c
*/

int f(double x);

int h() {
  int x = f(2.0);
  return x;
}
