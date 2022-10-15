void f(int g)
{
  g++;
  g--;
  
}

int main(int argc, char **argv)
{
  int i = 3;

  if( i > 0)
    {
      while(--i);
    }
  else
    {
      f(3);
    }
  
  return 0;
}
