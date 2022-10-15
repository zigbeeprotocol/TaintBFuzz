#include <stdarg.h>

int global = 0;

/*@ requires n>= 0; */
void f(int n, ...){
  int i;
  va_list list;
  va_start(list, n);
  for(i = 0; i<n; i++) {
    global += va_arg(list, int);
  }
  va_end(list);
}

/*@ requires n>= 0; */
void g(int n, ...){
  int i;
  va_list list;
  va_start(list, n);
  for(i = 0; i<n; i++) {
    global *= va_arg(list, int);
  }
  va_end(list);
}

void (*applications[2])(int n, ...) = {&f, &g};

int main() {
  void (*p)(int n, ...) = &f;
  f(1,1);
  p(3,0,1,2);
  applications[1](2,2,3);
  applications[0](3,4,5,9);
  return global;
}

