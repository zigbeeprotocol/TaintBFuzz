int x, y, z, t, *p, *q;
void main(int c)
{
  if (c&1)
    y = x + x++;
  p = c&2 ? &x : &t;
  y = *p + x++;
  q = c&4 ? &z : &t;
  y = *q + x++;
}
