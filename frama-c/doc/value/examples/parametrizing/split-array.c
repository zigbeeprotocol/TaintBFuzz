int t1[] = {1, 2, 3}, t2[] = {4, 5}, t3[] = {6, 7, 8, 9};
int *t[] = {t1, t2, t3};
int sizes[] = {3, 2, 4};
/*@ requires 0 <= i < 3; */
int main(int i)
{
  int S = 0;
  //@ split i;
  //@ loop unroll sizes[i];
  for (int j = 0 ; j < sizes[i] ; j++)
    S += t[i][j];

  return S;
}
