/* run.config*
   STDOPT: #"-eva-alloc-functions alloc -eva-mlevel 0"
*/
#include <stdlib.h>
#define N 2000

int t[N];

void f() {
  for (int i=0; i<N; i++)
    t[i] = i;
}

int *alloc() {
  return malloc(4);
}

int *k() {
  return alloc();
}

void main() {
  f();
  f();
  f();
  Frama_C_show_each(t[1]);
  Frama_C_show_each(t[1]);
  Frama_C_show_each(t[2]);
  f();

  int *p1 = alloc();
  int *p2 = alloc();

  int *p3 = k();
  int *p4 = k();

}
