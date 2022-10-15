/* run.config
   OPT: -json-compilation-database %{dep:@PTEST_DIR@/no-stdio.json} -print
*/

// no-stdio.json must have "-includestdio.h" and define ZERO

//@ ensures \result == ZERO;
int main(){
  printf("bla\n");
  return ZERO;
}
