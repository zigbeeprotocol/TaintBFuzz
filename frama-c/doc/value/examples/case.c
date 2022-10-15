int A;

//@ requires x >= 0 || x <= 0;
int square(int x)
{
  A = x;
  //@ assert x <= 0 || x > 0;

  return x * x;
}

void main (int x)
{
  square(x);
}
