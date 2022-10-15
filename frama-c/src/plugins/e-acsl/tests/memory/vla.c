/* run.config
   COMMENT: check variable-length arrays
   STDOPT: +"-eva-precision=1"
*/

int LEN = 10;

int main(int argc, char **argv) {
  int arr[LEN];
  int i;
  for (i = 0; i <= LEN; i++) {
    if (i < LEN) {
      /*@ assert \valid(&arr[i]); */
    } else {
      /*@ assert ! \valid(&arr[i]); */
    }
  }
  return 0;
}
