#include <stdint.h>
#include <stdio.h>

void main() {
  int a[2] = {1, 2};
  int *b = (int *)(((uintptr_t)a)*2);
  int nb_printed = printf("%d", (int)b);
  Frama_C_show_each_nb_printed(nb_printed); // must NOT contain a garbled mix
  b = 0; // minimize diffs in test oracle
}
