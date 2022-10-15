double fabs(double x)
{
  return x < 0.0 ? -x : x;
}

double main(double y)
{
  //@ split y < 0.0;
  if (fabs(y) > 1.0)
    y = y < 0 ? -1.0 : 1.0;
  //@ merge y < 0.0;
  return y;
}
