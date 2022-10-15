int i, t[10], *p;
void main()
{
  for (i=0; i<=10; i++)
    if (unknownfun()) t[i] = i;
  p = t + 12;
  if (unknownfun()) *p = i;
  p[-6] = i;
}
