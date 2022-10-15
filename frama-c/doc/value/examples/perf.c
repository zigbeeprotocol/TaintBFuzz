int x, y;


void ff(void)
{
  x++;
}

void g(void)
{
  ff();
  ff();
  ff();
  ff();
  ff();
  ff();
  ff();
  ff();
  ff();
  ff();
  ff();
  ff();
  ff();
  ff();
  ff();
  ff();
}

void h(void)
{
  g();
  g();
  g();
  g();
  g();
  g();
  g();
  g();
  g();
  g();
  g();
  g();
  g();
  g();
  g();
  g();
}

void i(void)
{
  h();
  h();
  h();
  h();
  h();
  h();
  h();
  h();
  h();
  h();
  h();
  h();
  h();
  h();
  h();
  h();
}

void j(void)
{
  i();
  i();
  i();
  i();
  i();
  i();
  i();
  i();
  i();
  i();
  i();
  i();
  i();
  i();
  i();
  i();
}

int main(void)
{
  j();
}
