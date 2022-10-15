/* Generated by Frama-C */
#include "pthread.h"
#include "sched.h"
#include "signal.h"
#include "stddef.h"
#include "stdint.h"
#include "stdio.h"
#include "time.h"
extern  __attribute__((__FC_BUILTIN__)) int __e_acsl_sound_verdict;

long A = (long)0;
int main(void)
{
  int __retres;
  __e_acsl_memory_init((int *)0,(char ***)0,8UL);
  {
    __e_acsl_mpz_t __gen_e_acsl_A;
    __e_acsl_mpz_t __gen_e_acsl_;
    __e_acsl_mpz_t __gen_e_acsl_mul;
    long __gen_e_acsl__2;
    __e_acsl_mpz_t __gen_e_acsl__3;
    __e_acsl_mpz_t __gen_e_acsl_add;
    __e_acsl_mpz_t __gen_e_acsl__4;
    int __gen_e_acsl_eq;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data = {.values = (void *)0};
    __e_acsl_assert_register_long(& __gen_e_acsl_assert_data,"A",0,A);
    __gmpz_init_set_si(__gen_e_acsl_A,A);
    __gmpz_init_set_si(__gen_e_acsl_,3L);
    __e_acsl_assert_register_long(& __gen_e_acsl_assert_data,"A",0,A);
    __gmpz_init(__gen_e_acsl_mul);
    __gmpz_mul(__gen_e_acsl_mul,(__e_acsl_mpz_struct const *)(__gen_e_acsl_),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl_A));
    __gen_e_acsl__2 = __gmpz_get_si((__e_acsl_mpz_struct const *)(__gen_e_acsl_mul));
    /*@ assert
        Eva: signed_overflow: -9223372036854775808 <= __gen_e_acsl__2 - 1;
    */
    __gmpz_init_set_si(__gen_e_acsl__3,__gen_e_acsl__2 - 1L);
    __gmpz_init(__gen_e_acsl_add);
    __gmpz_add(__gen_e_acsl_add,
               (__e_acsl_mpz_struct const *)(__gen_e_acsl_A),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl__3));
    __gmpz_init_set_si(__gen_e_acsl__4,(long)(-1));
    __gen_e_acsl_eq = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_add),
                                 (__e_acsl_mpz_struct const *)(__gen_e_acsl__4));
    __gen_e_acsl_assert_data.blocking = 1;
    __gen_e_acsl_assert_data.kind = "Assertion";
    __gen_e_acsl_assert_data.pred_txt = "A + (long)((long)(3 * A) - 1) == -1";
    __gen_e_acsl_assert_data.file = "bts2231.i";
    __gen_e_acsl_assert_data.fct = "main";
    __gen_e_acsl_assert_data.line = 8;
    __e_acsl_assert(__gen_e_acsl_eq == 0,& __gen_e_acsl_assert_data);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data);
    __gmpz_clear(__gen_e_acsl_A);
    __gmpz_clear(__gen_e_acsl_);
    __gmpz_clear(__gen_e_acsl_mul);
    __gmpz_clear(__gen_e_acsl__3);
    __gmpz_clear(__gen_e_acsl_add);
    __gmpz_clear(__gen_e_acsl__4);
  }
  /*@ assert A + (long)((long)(3 * A) - 1) == -1; */ ;
  __retres = 0;
  __e_acsl_memory_clean();
  return __retres;
}


