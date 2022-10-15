int x,y;
int f(void)
{
  return (int) &x + (int) &y;
}
