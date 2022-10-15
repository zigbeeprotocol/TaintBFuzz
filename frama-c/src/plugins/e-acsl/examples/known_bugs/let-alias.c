/* run.config_dev
   DONTRUN:
*/

/* let binding on alias: only work with -e-acsl-full-mtracking;
   should not be the case. */

int main(void) {
  int t[4] = {1,2,3,4};
  /*@ assert \let u = t + 1; *(u + 2) == 4; */ ;
  /*@ assert (\let u = t + 1; *(u + 2)) == 4; */ ;
  return 0;
}
