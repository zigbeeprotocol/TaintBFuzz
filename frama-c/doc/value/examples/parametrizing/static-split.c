#include "__fc_builtin.h"
void main(void) {
  int t[12] = {0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89};
  int i = Frama_C_interval(0, 10);
  //@ split i;
  int x = t[i];
  int y = t[i+1];
  i = 0;
  int r = y - x;
  //@ assert r >= 0;
  //@ merge i;
}
