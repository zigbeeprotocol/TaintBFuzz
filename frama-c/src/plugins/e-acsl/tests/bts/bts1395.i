/* run.config
   COMMENT: recursive function
   STDOPT: +"-eva-unroll-recursive-calls 5"
*/

/*@ requires n > 0; */
int fact(int n) {
  if (n == 1)
    return 1;
  return n * fact(n - 1);
}

int main() {
  int x = fact(5);
  /*@ assert x == 120; */
  return 0;
}
