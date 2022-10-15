int i,j;

void main(void)
{
  int n = 13;
  for (i=0; i<n; i++)
    /*@ widen_hints i, 12, 13; */
    j = 4 * i + 7;
}
