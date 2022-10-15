int N;

/*@
  ensures N == 4;
  assigns N, p[0..\at(N,Post)-1];
*/
void job1(int *p)
{
  N = 0;
  p[N++] = 0;
  p[N++] = 0;
  p[N++] = 0;
  p[N++] = 0;
}

int A[4];

/*@
  ensures N == 4;
  assigns N, *(p + A[0..\at(N,Post)-1]);
*/
void job2(int *p)
{
  N = 0;
  p[A[N++]] = 0;
  p[A[N++]] = 0;
  p[A[N++]] = 0;
  p[A[N++]] = 0;
}

/*@
  requires 0 <= N;
  assigns N, p[0..\at(N,Post)];
*/
void job3(int *p)
{
  /*@
    loop invariant 0 <= i <= N;
    loop assigns i, p[0..N-1];
   */
  for (int i = 0; i < N; i++)
    p[i] = 0;
  N++;
}
