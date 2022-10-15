int x,y;
int *t[2] = { &x, &y };

int main(void)
{
  return * (int*) ((unsigned long) t + 6);
}
