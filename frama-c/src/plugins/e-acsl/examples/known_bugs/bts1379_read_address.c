
#include "stdio.h"

int x = 2, y = 3, z = 5, t[2];

int main() {
  //@ assert \valid(&x) && \valid(&y) && \valid(&z);
  int * p = &t;

  //@ assert \valid(p);
  //@ assert \base_addr(p) == \base_addr(&t);
  *p = 4;
  p++;

  //@ assert \valid(p);
  //@ assert \base_addr(p) == \base_addr(&t);
  *p = 12;
  p++;

  //@ assert !\valid(p);
  printf("%i %i\n", t[0], t[1]);

  //===================================
  p = &y;
  printf("%p %p %p %p\n", &x, &y, &z, p);
  printf("%i %i %i %i\n", x, y, z, *p);

  //@ assert \valid(p);
  p++;

  printf("%p %p %p %p\n", &x, &y, &z, p);
  printf("%i %i %i %i\n", x, y, z, *p);
  
  //@ assert \valid(p);
  //@ assert \base_addr(p) == \base_addr(&y);
  *p = 100;
  printf("%i %i %i %i\n", x, y, z, *p);
  return 0;
}
