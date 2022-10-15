#include "__fc_builtin.h"

int main()
{
  float f = Frama_C_float_interval(2e9, 3e9);
  return (int) f;
}

