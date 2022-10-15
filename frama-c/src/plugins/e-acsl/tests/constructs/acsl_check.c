/* run.config_dev
   MACRO: ROOT_EACSL_GCC_OPTS_EXT -F -no-unicode
*/
#include <stdio.h>

/*@
  check requires a != 0;
  check ensures \result != 0;
*/
int f(int a) {
  return a;
}

void g(int a, int *b) {
  //@ check a / b[1] == 0;
}

int main() {
  int a = 0;
  int b[] = {1, 2, 3};
  //@ check a == 1;
  a = f(a);
  fprintf(stderr, "SHOULD BE PRINTED IN EXECUTION LOG\n");
  // Check that the RTEs are blocking even if the check is not.
  g(a, b);
  // Admits clauses are not translated
  //@ admit a == 1;
  //@ admit a == 2;
  return a;
}
