/* Generated by Frama-C */
#include "pthread.h"
#include "sched.h"
#include "signal.h"
#include "stddef.h"
#include "stdint.h"
#include "stdio.h"
#include "time.h"
extern  __attribute__((__FC_BUILTIN__)) int __e_acsl_sound_verdict;

int main(void)
{
  int __retres;
  int x;
  __e_acsl_memory_init((int *)0,(char ***)0,8UL);
  {
    __e_acsl_assert_data_t __gen_e_acsl_assert_data = {.values = (void *)0};
    __gen_e_acsl_assert_data.blocking = 1;
    __gen_e_acsl_assert_data.kind = "Assertion";
    __gen_e_acsl_assert_data.pred_txt = "0 == 0";
    __gen_e_acsl_assert_data.file = "integer_constant.i";
    __gen_e_acsl_assert_data.fct = "main";
    __gen_e_acsl_assert_data.line = 6;
    __e_acsl_assert(1,& __gen_e_acsl_assert_data);
  }
  /*@ assert 0 == 0; */ ;
  x = 0;
  x ++;
  {
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_2 =
      {.values = (void *)0};
    __gen_e_acsl_assert_data_2.blocking = 1;
    __gen_e_acsl_assert_data_2.kind = "Assertion";
    __gen_e_acsl_assert_data_2.pred_txt = "0 != 1";
    __gen_e_acsl_assert_data_2.file = "integer_constant.i";
    __gen_e_acsl_assert_data_2.fct = "main";
    __gen_e_acsl_assert_data_2.line = 8;
    __e_acsl_assert(1,& __gen_e_acsl_assert_data_2);
  }
  /*@ assert 0 != 1; */ ;
  {
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_3 =
      {.values = (void *)0};
    __gen_e_acsl_assert_data_3.blocking = 1;
    __gen_e_acsl_assert_data_3.kind = "Assertion";
    __gen_e_acsl_assert_data_3.pred_txt = "1152921504606846975 == 0xfffffffffffffff";
    __gen_e_acsl_assert_data_3.file = "integer_constant.i";
    __gen_e_acsl_assert_data_3.fct = "main";
    __gen_e_acsl_assert_data_3.line = 9;
    __e_acsl_assert(1,& __gen_e_acsl_assert_data_3);
  }
  /*@ assert 1152921504606846975 == 0xfffffffffffffff; */ ;
  {
    __e_acsl_mpz_t __gen_e_acsl_;
    int __gen_e_acsl_eq;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_4 =
      {.values = (void *)0};
    __gmpz_init_set_str(__gen_e_acsl_,
                        "340282366920938463463374607431768211455",10);
    __gen_e_acsl_eq = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_),
                                 (__e_acsl_mpz_struct const *)(__gen_e_acsl_));
    __gen_e_acsl_assert_data_4.blocking = 1;
    __gen_e_acsl_assert_data_4.kind = "Assertion";
    __gen_e_acsl_assert_data_4.pred_txt = "0xffffffffffffffffffffffffffffffff == 0xffffffffffffffffffffffffffffffff";
    __gen_e_acsl_assert_data_4.file = "integer_constant.i";
    __gen_e_acsl_assert_data_4.fct = "main";
    __gen_e_acsl_assert_data_4.line = 11;
    __e_acsl_assert(__gen_e_acsl_eq == 0,& __gen_e_acsl_assert_data_4);
    __gmpz_clear(__gen_e_acsl_);
  }
  /*@
  assert
  0xffffffffffffffffffffffffffffffff == 0xffffffffffffffffffffffffffffffff;
   */
  ;
  __retres = 0;
  __e_acsl_memory_clean();
  return __retres;
}

