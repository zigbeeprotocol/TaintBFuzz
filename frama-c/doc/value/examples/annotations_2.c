//@ requires a == &b || a == &c;
int generalization(int *a, int b, int c)
{
  b = 5;
  c = 4;
  *(int*)a = 3;
  return b;
}

//@ requires d != 0;
int not_reduced(int d)
{
  return d;
}
