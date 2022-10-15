/* run.config
   COMMENT: Test option -cg-function-pointers
   MODULE: @PTEST_NAME@
   PLUGIN: @PTEST_PLUGIN@,eva
   OPT: -cg-function-pointers
   OPT: -cg-no-services -cg-function-pointers
   OPT: -cg-no-function-pointers
   OPT: -cg-no-services -cg-no-function-pointers
*/

int (*fptr)(int);

int f(int x) { return x; }
int g(int x) { return x-1; }

int main(void) {
  int x = 0;
  fptr = f;
  x = (*fptr)(1);
  fptr = g;
  x = (*fptr)(1);
  return x;
}
