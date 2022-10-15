/* run.config
   COMMENT: \separated
 */

#include <stdlib.h>

int main() {
  // Stack memory on different blocks
  {
    int a, b, c;
    a = b = c = 0;
    int *d = &a;

    //@ assert \separated(&a, &b, &c);
    //@ assert !\separated(&a, &b, &c, d);
  }

  // Stack memory on the same block
  {
    double array[20] = {0};
    //@ assert \separated(array+(0..9), array+(10..19));
    //@ assert !\separated(&array[0..10], &array[5..15]);
    //@ assert !\separated(array+(0..19), array+(5..15));
    //@ assert \separated(&array[0], &array[1]);
    //@ assert !\separated(array+(0..1), array+(1..2));
    //@ assert \separated(&array[15..5], &array[0..19]);
    //@ assert \separated(array+(0..-3), array+(0..19));
  }

  // Heap memory on different blocks
  {
    int *a = malloc(sizeof(int));
    int *b = malloc(sizeof(int));
    int *c = a;

    //@ assert \separated(a, b);
    //@ assert !\separated(a, b, c);

    free(a);
    free(b);
  }

  // Heap memory on the same block
  {
    double *array = malloc(sizeof(double[20]));
    //@ assert \separated(&array[0..9], &array[10..19]);
    //@ assert !\separated(array+(0..10), array+(5..15));
    //@ assert !\separated(&array[0..19], &array[5..15]);
    //@ assert \separated(array+(0), array+(1));
    //@ assert !\separated(&array[0..1], &array[1..2]);
    //@ assert \separated(array+(15..5), array+(0..19));
    //@ assert \separated(&array[0..-3], &array[0..19]);
    free(array);
  }

  // Non-contiguous memory locations
  {
    double array[10][10][10] = {0};

    //@ assert \separated(&array[0][0..2][0], &array[0][3..5][0], &array[0][6..9][0]);
    //@ assert \separated(&array[0][0..2][0], &array[1][0..2][0], &array[2][0..2][0]);
    //@ assert \separated(&array[0..2][0..2][0], &array[0..2][3..5][0]);
    //@ assert !\separated(&array[0..3][0..2][0], &array[3..5][0..2][0]);
    //@ assert \separated(&array[0..3][2..0][0], &array[3..5][0..2][0]);
  }

  return 0;
}
