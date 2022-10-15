void foo(int *p) {
  /*@assert \valid(p); */
  *p = 1;
}

void bar(int *p) {
  foo(p);
}

int main(void) {
  int i = 0;
  int *p = &i;
  bar(p+1);
  return 0;
}

