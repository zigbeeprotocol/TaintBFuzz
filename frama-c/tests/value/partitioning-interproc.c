/* run.config*

   STDOPT: #"-main cassign_test -eva-partition-history 1 -eva-interprocedural-history"
   STDOPT: #"-main fabs_test -eva-partition-history 1 -eva-domains equality -eva-interprocedural-history"
   STDOPT: #"-main fabs_splits_test -eva-partition-history 1 -eva-domains equality -eva-interprocedural-splits"
   */
#include "__fc_builtin.h"

int cassign(int *p)
{
  if (Frama_C_nondet(0,1))
  {
    *p = 0;
    return 1;
  }

  return 0;
}

void cassign_test(void) {
  int x, y;

  // First call
  if (cassign(&x)) {
    y = x + 1;
    Frama_C_show_each(y);
  }

  // Second call with some MemExec hit
  if (cassign(&x)) {
    y = x + 1;
    Frama_C_show_each(y);
  }
}


double fabs(double x)
{
  if (x == 0.0) {
    return 0.0;
  } else if (x > 0.0) {
    return x;
  } else {
    return -x;
  } 
}

void fabs_test(double x)
{
  if (fabs(x) > 1.0) {
    x = x < 0 ? -1.0 : 1.0;
  }
}


double fabs_splits(double x)
{
  //@ split x > 0.0;
  //@ split x < 0.0;
  if (x == 0.0) {
    return 0.0;
  } else if (x > 0.0) {
    return x;
  } else {
    return -x;
  } 
}

void fabs_splits_test(double x)
{
  if (fabs_splits(x) > 1.0) {
    x = x < 0 ? -1.0 : 1.0;
  }
}
