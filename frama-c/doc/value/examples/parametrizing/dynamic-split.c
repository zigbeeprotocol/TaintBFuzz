#include "__fc_builtin.h"
void test2(void){
  int t[12] = {0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89};
  int i = Frama_C_interval(0, 10);
  //@ dynamic_split i;
  while (i < 11) {
    int x = t[i];
    int y = t[i+1];
    int r = y - x;
    //@ assert r >= 0;
    i++;
  }
  //@ merge i;
}
