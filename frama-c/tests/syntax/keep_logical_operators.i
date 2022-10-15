/* run.config 
   OPT:-print -keep-logical-operators
*/
int test(int a, int b, int c) {

  if (a && (b || c)) {
    return 1;
  }
  return 2;

}

int test_ptr(int* a, int* b, int* c) {
  if (a && (b || c)) {
    return 1;
  }
  if (a)
    if (b)
      return 2;
  return 3;
}
