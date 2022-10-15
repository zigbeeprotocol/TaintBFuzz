#include "__fc_builtin.h"

int main(void)
{
  int x = Frama_C_interval(-10, 10);
  //@ assert x <= 0 || x >= 0 ;
  return x * x;
}
