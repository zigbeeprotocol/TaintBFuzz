/* run.config
   COMMENT: Array overflow
*/

#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>

struct dat {
  int arr[4];
};

struct dat2 {
  struct dat *p[2];
};

struct dat3 {
  int *arr;
};

void init4(int *arr, int start) {
  for (int i = 0; i < 4; ++i) {
    arr[i] = start + i;
  }
}

int main() {
  int a[4] = {1, 2, 3, 4};
  int b[4] = {5, 6, 7, 8};

  /*@ assert ! \valid(&a[4]); */

  int *ap = a;
  int *bp = b;

  /*@ assert ! \valid(&((int[])ap)[4]); */

  struct dat d = {.arr = {4, 5, 6, 7}};
  struct dat dd = {.arr = {1, 2, 3, 9}};
  struct dat2 d2 = {.p = {&d, &dd}};

  /*@ assert ! \valid(&d.arr[4]); */
  /*@ assert \valid(&d2.p[1]->arr[2]); */

  return 0;
}
