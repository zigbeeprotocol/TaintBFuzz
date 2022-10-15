int *f(int c)
{
  int r, t, *p;
  if (c) r = 2;
  t = r + 3;
  return &t;
}

int main(int c)
{
  int *p;
  p = f(c);  
  return *p;
}
