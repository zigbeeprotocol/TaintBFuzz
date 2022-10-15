int t1[] = {1, 2, 3}, t2[] = {4, 5}, t3[] = {6, 7, 8, 9};
int *t[] = {t1, t2, t3};
int sizes[] = {3, 2, 4};
void main(void)
{
  int S = 0;
  //@ loop unroll 3;
  for (int i = 0 ; i < 3 ; i++) {
    //@ loop unroll sizes[i];
    for (int j = 0 ; j < sizes[i] ; j++) {
      S += t[i][j];
    }
  }
}
