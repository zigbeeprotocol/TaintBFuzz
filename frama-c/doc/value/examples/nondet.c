#include "__fc_builtin.h"

int A,B,X;
void main(void)
{
  A = Frama_C_nondet(6, 15);
  B = Frama_C_interval(-3, 10);
  X = A * B;
}
