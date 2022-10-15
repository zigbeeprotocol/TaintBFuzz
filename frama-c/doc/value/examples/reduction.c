int t[10],u[10];

void f(int x)
{
  int i;
  for (i=0; i<10; i++)
    {
      //@ assert x >= 0 && x < 10;
      t[i] = u[x];
    }
}
