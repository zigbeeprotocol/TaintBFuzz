int x, y = 50;
void main()
{
  while(y<100)
    y = y + (100 - y)/2;
  x = y;
}
