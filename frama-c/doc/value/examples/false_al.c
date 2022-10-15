int x,y,z,r,i,t[101]={1,2,3};

void main(void)
{
  x = Frama_C_interval(-10,10);
  i = x * x;
  y = t[i];
  r = 7 / (y + 1);
  z = 3 / y;
}
