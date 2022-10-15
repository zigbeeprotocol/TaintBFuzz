int i,j;

void main(void)
{
  int n = 13;
  /*@ loop pragma WIDEN_HINTS i, 12, 13; */
  for (i=0; i<n; i++)
    j = 4 * i + 7;
}