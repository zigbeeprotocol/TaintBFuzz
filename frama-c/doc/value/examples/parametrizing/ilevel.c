#include "__fc_builtin.h"

int t[12] = {2, 3, 5, 7, 11, 13, 17, 19, 23, 27, 29, 31};

int main()
{
  return t[Frama_C_interval(0, 11)];
}
