/* Generated by Frama-C */
#include "pthread.h"
#include "sched.h"
#include "signal.h"
#include "stddef.h"
#include "stdint.h"
#include "stdio.h"
#include "time.h"
extern  __attribute__((__FC_BUILTIN__)) int __e_acsl_sound_verdict;

/*@ requires n > 0; */
int __gen_e_acsl_fact(int n);

int fact(int n)
{
  int __retres;
  int tmp;
  if (n == 1) {
    __retres = 1;
    goto return_label;
  }
  tmp = __gen_e_acsl_fact(n - 1);
  ;
  __retres = n * tmp;
  return_label: return __retres;
}

int main(void)
{
  int __retres;
  __e_acsl_memory_init((int *)0,(char ***)0,8UL);
  int x = __gen_e_acsl_fact(5);
  {
    __e_acsl_assert_data_t __gen_e_acsl_assert_data = {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,"x",0,x);
    __gen_e_acsl_assert_data.blocking = 1;
    __gen_e_acsl_assert_data.kind = "Assertion";
    __gen_e_acsl_assert_data.pred_txt = "x == 120";
    __gen_e_acsl_assert_data.file = "bts1395.i";
    __gen_e_acsl_assert_data.fct = "main";
    __gen_e_acsl_assert_data.line = 15;
    __e_acsl_assert(x == 120,& __gen_e_acsl_assert_data);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data);
  }
  /*@ assert x == 120; */ ;
  __retres = 0;
  __e_acsl_memory_clean();
  return __retres;
}

/*@ requires n > 0; */
int __gen_e_acsl_fact(int n)
{
  int __retres;
  {
    __e_acsl_assert_data_t __gen_e_acsl_assert_data = {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,"n",0,n);
    __gen_e_acsl_assert_data.blocking = 1;
    __gen_e_acsl_assert_data.kind = "Precondition";
    __gen_e_acsl_assert_data.pred_txt = "n > 0";
    __gen_e_acsl_assert_data.file = "bts1395.i";
    __gen_e_acsl_assert_data.fct = "fact";
    __gen_e_acsl_assert_data.line = 6;
    __e_acsl_assert(n > 0,& __gen_e_acsl_assert_data);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data);
  }
  __retres = fact(n);
  return __retres;
}


