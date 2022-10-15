#define NROWS 10
void main(void)
{
  int a[NROWS][20] = {0};
  //@ loop unroll NROWS;
  for (int i = 0; i < 10; i++) {
    //@ loop unroll (10+10);
    for (int j = 0; j < 20; j++) {
      a[i][j] += i + j;
    }
  }
}
