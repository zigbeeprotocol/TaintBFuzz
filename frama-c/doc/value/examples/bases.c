int x, y;
int *p = &y;

void main(int c) {
  if (c)
    x = 2;
  else {
    while (p != &x) p++;
    *p = 3;
    }
}
