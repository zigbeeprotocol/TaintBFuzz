extern int f(void);

int main(void) {
  for (; 1; (void)(4 > f()))
    continue;

  for (int a; 1; (void)(a > f()))
    continue;

  for (; 1; (void)(f() > f()))
    continue;

  for (int a; 1; a++)
    continue;

  return 0;
}
