int y, z=1;
int f(int x) {
  y = x + 1;
  return y;
}

void main(void) {
  for (y=0; y<2+2; y++)
    z=f(y);
}
