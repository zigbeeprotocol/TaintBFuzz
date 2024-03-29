/* Generated by Frama-C */
#include "pthread.h"
#include "sched.h"
#include "signal.h"
#include "stddef.h"
#include "stdint.h"
#include "stdio.h"
#include "time.h"
extern  __attribute__((__FC_BUILTIN__)) int __e_acsl_sound_verdict;

/*@ logic integer f1(integer n) = n <= 0? 0: f1(n - 1) + n;

*/
void __gen_e_acsl_f1(__e_acsl_mpz_t *__retres_arg, int n);

void __gen_e_acsl_f1_2(__e_acsl_mpz_t *__retres_arg, long n);

void __gen_e_acsl_f1_3(__e_acsl_mpz_t *__retres_arg, __e_acsl_mpz_struct * n);

/*@
logic integer f2(integer n) = n < 0? 1: (f2(n - 1) * f2(n - 2)) / f2(n - 3);

*/
int __gen_e_acsl_f2(int n);

int __gen_e_acsl_f2_2(long n);

int __gen_e_acsl_f2_3(__e_acsl_mpz_struct * n);

/*@ logic integer g(integer n) = 0;

*/
int __gen_e_acsl_g(int n);

int __gen_e_acsl_g_3(long n);

int __gen_e_acsl_g_5(__e_acsl_mpz_struct * n);

/*@ logic integer f3(integer n) = n > 0? g(n) * f3(n - 1) - 5: g(n + 1);

*/
int __gen_e_acsl_f3(int n);

int __gen_e_acsl_f3_2(long n);

int __gen_e_acsl_f3_3(__e_acsl_mpz_struct * n);

/*@
logic integer f4(integer n) =
  n < 100? f4(n + 1): (n < 0x7fffffffffffffffL? 0x7fffffffffffffffL: 6);

*/
unsigned long __gen_e_acsl_f4(int n);

unsigned long __gen_e_acsl_f4_2(long n);

unsigned long __gen_e_acsl_f4_3(__e_acsl_mpz_struct * n);

/*@ logic integer f5(integer n) = n >= 0? 0: f5(n + 1) + n;

*/
void __gen_e_acsl_f5(__e_acsl_mpz_t *__retres_arg, int n);

void __gen_e_acsl_f5_2(__e_acsl_mpz_t *__retres_arg, long n);

void __gen_e_acsl_f5_3(__e_acsl_mpz_t *__retres_arg, __e_acsl_mpz_struct * n);

int main(void)
{
  int __retres;
  __e_acsl_memory_init((int *)0,(char ***)0,8UL);
  {
    __e_acsl_mpz_t __gen_e_acsl_f1_8;
    __e_acsl_mpz_t __gen_e_acsl__7;
    int __gen_e_acsl_eq;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data = {.values = (void *)0};
    __gen_e_acsl_f1(& __gen_e_acsl_f1_8,0);
    __e_acsl_assert_register_mpz(& __gen_e_acsl_assert_data,"f1(0)",0,
                                 (__e_acsl_mpz_struct const *)(__gen_e_acsl_f1_8));
    __gmpz_init_set_si(__gen_e_acsl__7,0L);
    __gen_e_acsl_eq = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_f1_8),
                                 (__e_acsl_mpz_struct const *)(__gen_e_acsl__7));
    __gen_e_acsl_assert_data.blocking = 1;
    __gen_e_acsl_assert_data.kind = "Assertion";
    __gen_e_acsl_assert_data.pred_txt = "f1(0) == 0";
    __gen_e_acsl_assert_data.file = "functions_rec.c";
    __gen_e_acsl_assert_data.fct = "main";
    __gen_e_acsl_assert_data.line = 28;
    __e_acsl_assert(__gen_e_acsl_eq == 0,& __gen_e_acsl_assert_data);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data);
    __gmpz_clear(__gen_e_acsl_f1_8);
    __gmpz_clear(__gen_e_acsl__7);
  }
  /*@ assert f1(0) == 0; */ ;
  {
    __e_acsl_mpz_t __gen_e_acsl_f1_10;
    __e_acsl_mpz_t __gen_e_acsl__8;
    int __gen_e_acsl_eq_2;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_2 =
      {.values = (void *)0};
    __gen_e_acsl_f1(& __gen_e_acsl_f1_10,1);
    __e_acsl_assert_register_mpz(& __gen_e_acsl_assert_data_2,"f1(1)",0,
                                 (__e_acsl_mpz_struct const *)(__gen_e_acsl_f1_10));
    __gmpz_init_set_si(__gen_e_acsl__8,1L);
    __gen_e_acsl_eq_2 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_f1_10),
                                   (__e_acsl_mpz_struct const *)(__gen_e_acsl__8));
    __gen_e_acsl_assert_data_2.blocking = 1;
    __gen_e_acsl_assert_data_2.kind = "Assertion";
    __gen_e_acsl_assert_data_2.pred_txt = "f1(1) == 1";
    __gen_e_acsl_assert_data_2.file = "functions_rec.c";
    __gen_e_acsl_assert_data_2.fct = "main";
    __gen_e_acsl_assert_data_2.line = 29;
    __e_acsl_assert(__gen_e_acsl_eq_2 == 0,& __gen_e_acsl_assert_data_2);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_2);
    __gmpz_clear(__gen_e_acsl_f1_10);
    __gmpz_clear(__gen_e_acsl__8);
  }
  /*@ assert f1(1) == 1; */ ;
  {
    __e_acsl_mpz_t __gen_e_acsl_f1_12;
    __e_acsl_mpz_t __gen_e_acsl__9;
    int __gen_e_acsl_eq_3;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_3 =
      {.values = (void *)0};
    __gen_e_acsl_f1(& __gen_e_acsl_f1_12,100);
    __e_acsl_assert_register_mpz(& __gen_e_acsl_assert_data_3,"f1(100)",0,
                                 (__e_acsl_mpz_struct const *)(__gen_e_acsl_f1_12));
    __gmpz_init_set_si(__gen_e_acsl__9,5050L);
    __gen_e_acsl_eq_3 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_f1_12),
                                   (__e_acsl_mpz_struct const *)(__gen_e_acsl__9));
    __gen_e_acsl_assert_data_3.blocking = 1;
    __gen_e_acsl_assert_data_3.kind = "Assertion";
    __gen_e_acsl_assert_data_3.pred_txt = "f1(100) == 5050";
    __gen_e_acsl_assert_data_3.file = "functions_rec.c";
    __gen_e_acsl_assert_data_3.fct = "main";
    __gen_e_acsl_assert_data_3.line = 30;
    __e_acsl_assert(__gen_e_acsl_eq_3 == 0,& __gen_e_acsl_assert_data_3);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_3);
    __gmpz_clear(__gen_e_acsl_f1_12);
    __gmpz_clear(__gen_e_acsl__9);
  }
  /*@ assert f1(100) == 5050; */ ;
  {
    int __gen_e_acsl_f2_20;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_4 =
      {.values = (void *)0};
    __gen_e_acsl_f2_20 = __gen_e_acsl_f2(7);
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_4,"f2(7)",0,
                                 __gen_e_acsl_f2_20);
    __gen_e_acsl_assert_data_4.blocking = 1;
    __gen_e_acsl_assert_data_4.kind = "Assertion";
    __gen_e_acsl_assert_data_4.pred_txt = "f2(7) == 1";
    __gen_e_acsl_assert_data_4.file = "functions_rec.c";
    __gen_e_acsl_assert_data_4.fct = "main";
    __gen_e_acsl_assert_data_4.line = 32;
    __e_acsl_assert(__gen_e_acsl_f2_20 == 1,& __gen_e_acsl_assert_data_4);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_4);
  }
  /*@ assert f2(7) == 1; */ ;
  {
    int __gen_e_acsl_f3_8;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_8 =
      {.values = (void *)0};
    __gen_e_acsl_f3_8 = __gen_e_acsl_f3(6);
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_8,"f3(6)",0,
                                 __gen_e_acsl_f3_8);
    __gen_e_acsl_assert_data_8.blocking = 1;
    __gen_e_acsl_assert_data_8.kind = "Assertion";
    __gen_e_acsl_assert_data_8.pred_txt = "f3(6) == -5";
    __gen_e_acsl_assert_data_8.file = "functions_rec.c";
    __gen_e_acsl_assert_data_8.fct = "main";
    __gen_e_acsl_assert_data_8.line = 34;
    __e_acsl_assert(__gen_e_acsl_f3_8 == -5,& __gen_e_acsl_assert_data_8);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_8);
  }
  /*@ assert f3(6) == -5; */ ;
  {
    unsigned long __gen_e_acsl_f4_8;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_9 =
      {.values = (void *)0};
    __gen_e_acsl_f4_8 = __gen_e_acsl_f4(9);
    __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data_9,"f4(9)",0,
                                   __gen_e_acsl_f4_8);
    __gen_e_acsl_assert_data_9.blocking = 1;
    __gen_e_acsl_assert_data_9.kind = "Assertion";
    __gen_e_acsl_assert_data_9.pred_txt = "f4(9) > 0";
    __gen_e_acsl_assert_data_9.file = "functions_rec.c";
    __gen_e_acsl_assert_data_9.fct = "main";
    __gen_e_acsl_assert_data_9.line = 36;
    __e_acsl_assert(__gen_e_acsl_f4_8 > 0UL,& __gen_e_acsl_assert_data_9);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_9);
  }
  /*@ assert f4(9) > 0; */ ;
  {
    __e_acsl_mpz_t __gen_e_acsl_f5_8;
    __e_acsl_mpz_t __gen_e_acsl__32;
    int __gen_e_acsl_eq_4;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_10 =
      {.values = (void *)0};
    __gen_e_acsl_f5(& __gen_e_acsl_f5_8,0);
    __e_acsl_assert_register_mpz(& __gen_e_acsl_assert_data_10,"f5(0)",0,
                                 (__e_acsl_mpz_struct const *)(__gen_e_acsl_f5_8));
    __gmpz_init_set_si(__gen_e_acsl__32,0L);
    __gen_e_acsl_eq_4 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_f5_8),
                                   (__e_acsl_mpz_struct const *)(__gen_e_acsl__32));
    __gen_e_acsl_assert_data_10.blocking = 1;
    __gen_e_acsl_assert_data_10.kind = "Assertion";
    __gen_e_acsl_assert_data_10.pred_txt = "f5(0) == 0";
    __gen_e_acsl_assert_data_10.file = "functions_rec.c";
    __gen_e_acsl_assert_data_10.fct = "main";
    __gen_e_acsl_assert_data_10.line = 38;
    __e_acsl_assert(__gen_e_acsl_eq_4 == 0,& __gen_e_acsl_assert_data_10);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_10);
    __gmpz_clear(__gen_e_acsl_f5_8);
    __gmpz_clear(__gen_e_acsl__32);
  }
  /*@ assert f5(0) == 0; */ ;
  {
    long __gen_e_acsl_n_9;
    __e_acsl_mpz_t __gen_e_acsl_f5_10;
    __e_acsl_mpz_t __gen_e_acsl__33;
    int __gen_e_acsl_eq_5;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_11 =
      {.values = (void *)0};
    __gen_e_acsl_n_9 = 9223372036854775807L;
    __e_acsl_assert_register_long(& __gen_e_acsl_assert_data_11,"n",0,
                                  __gen_e_acsl_n_9);
    __gen_e_acsl_f5_2(& __gen_e_acsl_f5_10,__gen_e_acsl_n_9);
    __e_acsl_assert_register_mpz(& __gen_e_acsl_assert_data_11,"f5(n)",0,
                                 (__e_acsl_mpz_struct const *)(__gen_e_acsl_f5_10));
    __gmpz_init_set_si(__gen_e_acsl__33,0L);
    __gen_e_acsl_eq_5 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_f5_10),
                                   (__e_acsl_mpz_struct const *)(__gen_e_acsl__33));
    __gen_e_acsl_assert_data_11.blocking = 1;
    __gen_e_acsl_assert_data_11.kind = "Assertion";
    __gen_e_acsl_assert_data_11.pred_txt = "\\let n = 0 == 0? 0x7fffffffffffffffL: -1; f5(n) == 0";
    __gen_e_acsl_assert_data_11.file = "functions_rec.c";
    __gen_e_acsl_assert_data_11.fct = "main";
    __gen_e_acsl_assert_data_11.line = 40;
    __e_acsl_assert(__gen_e_acsl_eq_5 == 0,& __gen_e_acsl_assert_data_11);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_11);
    __gmpz_clear(__gen_e_acsl_f5_10);
    __gmpz_clear(__gen_e_acsl__33);
  }
  /*@ assert \let n = 0 == 0? 0x7fffffffffffffffL: -1; f5(n) == 0; */ ;
  __retres = 0;
  __e_acsl_memory_clean();
  return __retres;
}

/*@ assigns (*__retres_arg)[0];
    assigns (*__retres_arg)[0] \from n; */
void __gen_e_acsl_f1(__e_acsl_mpz_t *__retres_arg, int n)
{
  __e_acsl_mpz_t __gen_e_acsl_if_3;
  if (n <= 0) {
    __e_acsl_mpz_t __gen_e_acsl_;
    __gmpz_init_set_si(__gen_e_acsl_,0L);
    __gmpz_init_set(__gen_e_acsl_if_3,
                    (__e_acsl_mpz_struct const *)(__gen_e_acsl_));
    __gmpz_clear(__gen_e_acsl_);
  }
  else {
    __e_acsl_mpz_t __gen_e_acsl_f1_7;
    __e_acsl_mpz_t __gen_e_acsl_n_2;
    __e_acsl_mpz_t __gen_e_acsl_add_3;
    __gen_e_acsl_f1_2(& __gen_e_acsl_f1_7,n - 1L);
    __gmpz_init_set_si(__gen_e_acsl_n_2,(long)n);
    __gmpz_init(__gen_e_acsl_add_3);
    __gmpz_add(__gen_e_acsl_add_3,
               (__e_acsl_mpz_struct const *)(__gen_e_acsl_f1_7),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl_n_2));
    __gmpz_init_set(__gen_e_acsl_if_3,
                    (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_3));
    __gmpz_clear(__gen_e_acsl_f1_7);
    __gmpz_clear(__gen_e_acsl_n_2);
    __gmpz_clear(__gen_e_acsl_add_3);
  }
  __gmpz_init_set(*__retres_arg,
                  (__e_acsl_mpz_struct const *)(__gen_e_acsl_if_3));
  __gmpz_clear(__gen_e_acsl_if_3);
  return;
}

/*@ assigns (*__retres_arg)[0];
    assigns (*__retres_arg)[0] \from n; */
void __gen_e_acsl_f1_2(__e_acsl_mpz_t *__retres_arg, long n)
{
  __e_acsl_mpz_t __gen_e_acsl_if_2;
  if (n <= 0L) {
    __e_acsl_mpz_t __gen_e_acsl__2;
    __gmpz_init_set_si(__gen_e_acsl__2,0L);
    __gmpz_init_set(__gen_e_acsl_if_2,
                    (__e_acsl_mpz_struct const *)(__gen_e_acsl__2));
    __gmpz_clear(__gen_e_acsl__2);
  }
  else {
    __e_acsl_mpz_t __gen_e_acsl_n;
    __e_acsl_mpz_t __gen_e_acsl__3;
    __e_acsl_mpz_t __gen_e_acsl_sub;
    __e_acsl_mpz_t __gen_e_acsl_f1_6;
    __e_acsl_mpz_t __gen_e_acsl_add_2;
    __gmpz_init_set_si(__gen_e_acsl_n,n);
    __gmpz_init_set_si(__gen_e_acsl__3,1L);
    __gmpz_init(__gen_e_acsl_sub);
    __gmpz_sub(__gen_e_acsl_sub,
               (__e_acsl_mpz_struct const *)(__gen_e_acsl_n),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl__3));
    /*@ assert
        Eva: initialization:
          \initialized((__e_acsl_mpz_struct *)__gen_e_acsl_sub);
    */
    __gen_e_acsl_f1_3(& __gen_e_acsl_f1_6,
                      (__e_acsl_mpz_struct *)__gen_e_acsl_sub);
    __gmpz_init(__gen_e_acsl_add_2);
    __gmpz_add(__gen_e_acsl_add_2,
               (__e_acsl_mpz_struct const *)(__gen_e_acsl_f1_6),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl_n));
    __gmpz_init_set(__gen_e_acsl_if_2,
                    (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_2));
    __gmpz_clear(__gen_e_acsl_n);
    __gmpz_clear(__gen_e_acsl__3);
    __gmpz_clear(__gen_e_acsl_sub);
    __gmpz_clear(__gen_e_acsl_f1_6);
    __gmpz_clear(__gen_e_acsl_add_2);
  }
  __gmpz_init_set(*__retres_arg,
                  (__e_acsl_mpz_struct const *)(__gen_e_acsl_if_2));
  __gmpz_clear(__gen_e_acsl_if_2);
  return;
}

/*@ assigns (*__retres_arg)[0];
    assigns (*__retres_arg)[0] \from *((__e_acsl_mpz_struct *)n);
 */
void __gen_e_acsl_f1_3(__e_acsl_mpz_t *__retres_arg, __e_acsl_mpz_struct * n)
{
  __e_acsl_mpz_t __gen_e_acsl__4;
  int __gen_e_acsl_le;
  __e_acsl_mpz_t __gen_e_acsl_if;
  __gmpz_init_set_si(__gen_e_acsl__4,0L);
  __gen_e_acsl_le = __gmpz_cmp((__e_acsl_mpz_struct const *)(n),
                               (__e_acsl_mpz_struct const *)(__gen_e_acsl__4));
  if (__gen_e_acsl_le <= 0) {
    __e_acsl_mpz_t __gen_e_acsl__5;
    __gmpz_init_set_si(__gen_e_acsl__5,0L);
    __gmpz_init_set(__gen_e_acsl_if,
                    (__e_acsl_mpz_struct const *)(__gen_e_acsl__5));
    __gmpz_clear(__gen_e_acsl__5);
  }
  else {
    __e_acsl_mpz_t __gen_e_acsl__6;
    __e_acsl_mpz_t __gen_e_acsl_sub_2;
    __e_acsl_mpz_t __gen_e_acsl_f1_5;
    __e_acsl_mpz_t __gen_e_acsl_add;
    __gmpz_init_set_si(__gen_e_acsl__6,1L);
    __gmpz_init(__gen_e_acsl_sub_2);
    __gmpz_sub(__gen_e_acsl_sub_2,(__e_acsl_mpz_struct const *)(n),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl__6));
    /*@ assert
        Eva: initialization:
          \initialized((__e_acsl_mpz_struct *)__gen_e_acsl_sub_2);
    */
    __gen_e_acsl_f1_3(& __gen_e_acsl_f1_5,
                      (__e_acsl_mpz_struct *)__gen_e_acsl_sub_2);
    __gmpz_init(__gen_e_acsl_add);
    __gmpz_add(__gen_e_acsl_add,
               (__e_acsl_mpz_struct const *)(__gen_e_acsl_f1_5),
               (__e_acsl_mpz_struct const *)(n));
    __gmpz_init_set(__gen_e_acsl_if,
                    (__e_acsl_mpz_struct const *)(__gen_e_acsl_add));
    __gmpz_clear(__gen_e_acsl__6);
    __gmpz_clear(__gen_e_acsl_sub_2);
    __gmpz_clear(__gen_e_acsl_f1_5);
    __gmpz_clear(__gen_e_acsl_add);
  }
  __gmpz_init_set(*__retres_arg,
                  (__e_acsl_mpz_struct const *)(__gen_e_acsl_if));
  __gmpz_clear(__gen_e_acsl__4);
  __gmpz_clear(__gen_e_acsl_if);
  return;
}

/*@ assigns \result;
    assigns \result \from n; */
int __gen_e_acsl_f2(int n)
{
  int __gen_e_acsl_if_6;
  if (n < 0) __gen_e_acsl_if_6 = 1;
  else {
    int __gen_e_acsl_f2_15;
    int __gen_e_acsl_f2_17;
    int __gen_e_acsl_f2_19;
    __gen_e_acsl_f2_15 = __gen_e_acsl_f2_2(n - 1L);
    __gen_e_acsl_f2_17 = __gen_e_acsl_f2_2(n - 2L);
    __gen_e_acsl_f2_19 = __gen_e_acsl_f2_2(n - 3L);
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_7 =
      {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_7,
                                 "__gen_e_acsl_f2_19",0,__gen_e_acsl_f2_19);
    __gen_e_acsl_assert_data_7.blocking = 1;
    __gen_e_acsl_assert_data_7.kind = "RTE";
    __gen_e_acsl_assert_data_7.pred_txt = "__gen_e_acsl_f2_19 != 0";
    __gen_e_acsl_assert_data_7.file = "functions_rec.c";
    __gen_e_acsl_assert_data_7.fct = "f2";
    __gen_e_acsl_assert_data_7.line = 13;
    __gen_e_acsl_assert_data_7.name = "division_by_zero";
    __e_acsl_assert(__gen_e_acsl_f2_19 != 0,& __gen_e_acsl_assert_data_7);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_7);
    /*@ assert Eva: division_by_zero: __gen_e_acsl_f2_19 != 0; */
    /*@ assert
        Eva: signed_overflow:
          -2147483648 <= __gen_e_acsl_f2_15 * __gen_e_acsl_f2_17;
    */
    /*@ assert
        Eva: signed_overflow:
          __gen_e_acsl_f2_15 * __gen_e_acsl_f2_17 <= 2147483647;
    */
    /*@ assert
        Eva: signed_overflow:
          (int)(__gen_e_acsl_f2_15 * __gen_e_acsl_f2_17) / __gen_e_acsl_f2_19
          <= 2147483647;
    */
    __gen_e_acsl_if_6 = (__gen_e_acsl_f2_15 * __gen_e_acsl_f2_17) / __gen_e_acsl_f2_19;
  }
  return __gen_e_acsl_if_6;
}

/*@ assigns \result;
    assigns \result \from n; */
int __gen_e_acsl_f2_2(long n)
{
  int __gen_e_acsl_if_5;
  if (n < 0L) __gen_e_acsl_if_5 = 1;
  else {
    __e_acsl_mpz_t __gen_e_acsl_n_3;
    __e_acsl_mpz_t __gen_e_acsl__10;
    __e_acsl_mpz_t __gen_e_acsl_sub_3;
    int __gen_e_acsl_f2_10;
    __e_acsl_mpz_t __gen_e_acsl__15;
    __e_acsl_mpz_t __gen_e_acsl_sub_7;
    int __gen_e_acsl_f2_12;
    __e_acsl_mpz_t __gen_e_acsl__16;
    __e_acsl_mpz_t __gen_e_acsl_sub_8;
    int __gen_e_acsl_f2_14;
    __gmpz_init_set_si(__gen_e_acsl_n_3,n);
    __gmpz_init_set_si(__gen_e_acsl__10,1L);
    __gmpz_init(__gen_e_acsl_sub_3);
    __gmpz_sub(__gen_e_acsl_sub_3,
               (__e_acsl_mpz_struct const *)(__gen_e_acsl_n_3),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl__10));
    /*@ assert
        Eva: initialization:
          \initialized((__e_acsl_mpz_struct *)__gen_e_acsl_sub_3);
    */
    __gen_e_acsl_f2_10 = __gen_e_acsl_f2_3((__e_acsl_mpz_struct *)__gen_e_acsl_sub_3);
    __gmpz_init_set_si(__gen_e_acsl__15,2L);
    __gmpz_init(__gen_e_acsl_sub_7);
    __gmpz_sub(__gen_e_acsl_sub_7,
               (__e_acsl_mpz_struct const *)(__gen_e_acsl_n_3),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl__15));
    /*@ assert
        Eva: initialization:
          \initialized((__e_acsl_mpz_struct *)__gen_e_acsl_sub_7);
    */
    __gen_e_acsl_f2_12 = __gen_e_acsl_f2_3((__e_acsl_mpz_struct *)__gen_e_acsl_sub_7);
    __gmpz_init_set_si(__gen_e_acsl__16,3L);
    __gmpz_init(__gen_e_acsl_sub_8);
    __gmpz_sub(__gen_e_acsl_sub_8,
               (__e_acsl_mpz_struct const *)(__gen_e_acsl_n_3),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl__16));
    /*@ assert
        Eva: initialization:
          \initialized((__e_acsl_mpz_struct *)__gen_e_acsl_sub_8);
    */
    __gen_e_acsl_f2_14 = __gen_e_acsl_f2_3((__e_acsl_mpz_struct *)__gen_e_acsl_sub_8);
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_6 =
      {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_6,
                                 "__gen_e_acsl_f2_14",0,__gen_e_acsl_f2_14);
    __gen_e_acsl_assert_data_6.blocking = 1;
    __gen_e_acsl_assert_data_6.kind = "RTE";
    __gen_e_acsl_assert_data_6.pred_txt = "__gen_e_acsl_f2_14 != 0";
    __gen_e_acsl_assert_data_6.file = "functions_rec.c";
    __gen_e_acsl_assert_data_6.fct = "f2_2";
    __gen_e_acsl_assert_data_6.line = 13;
    __gen_e_acsl_assert_data_6.name = "division_by_zero";
    __e_acsl_assert(__gen_e_acsl_f2_14 != 0,& __gen_e_acsl_assert_data_6);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_6);
    /*@ assert Eva: division_by_zero: __gen_e_acsl_f2_14 != 0; */
    /*@ assert
        Eva: signed_overflow:
          -2147483648 <= __gen_e_acsl_f2_10 * __gen_e_acsl_f2_12;
    */
    /*@ assert
        Eva: signed_overflow:
          __gen_e_acsl_f2_10 * __gen_e_acsl_f2_12 <= 2147483647;
    */
    /*@ assert
        Eva: signed_overflow:
          (int)(__gen_e_acsl_f2_10 * __gen_e_acsl_f2_12) / __gen_e_acsl_f2_14
          <= 2147483647;
    */
    __gen_e_acsl_if_5 = (__gen_e_acsl_f2_10 * __gen_e_acsl_f2_12) / __gen_e_acsl_f2_14;
    __gmpz_clear(__gen_e_acsl_n_3);
    __gmpz_clear(__gen_e_acsl__10);
    __gmpz_clear(__gen_e_acsl_sub_3);
    __gmpz_clear(__gen_e_acsl__15);
    __gmpz_clear(__gen_e_acsl_sub_7);
    __gmpz_clear(__gen_e_acsl__16);
    __gmpz_clear(__gen_e_acsl_sub_8);
  }
  return __gen_e_acsl_if_5;
}

/*@ assigns \result;
    assigns \result \from *((__e_acsl_mpz_struct *)n); */
int __gen_e_acsl_f2_3(__e_acsl_mpz_struct * n)
{
  __e_acsl_mpz_t __gen_e_acsl__11;
  int __gen_e_acsl_lt;
  int __gen_e_acsl_if_4;
  __gmpz_init_set_si(__gen_e_acsl__11,0L);
  __gen_e_acsl_lt = __gmpz_cmp((__e_acsl_mpz_struct const *)(n),
                               (__e_acsl_mpz_struct const *)(__gen_e_acsl__11));
  if (__gen_e_acsl_lt < 0) __gen_e_acsl_if_4 = 1;
  else {
    __e_acsl_mpz_t __gen_e_acsl__12;
    __e_acsl_mpz_t __gen_e_acsl_sub_4;
    int __gen_e_acsl_f2_5;
    __e_acsl_mpz_t __gen_e_acsl__13;
    __e_acsl_mpz_t __gen_e_acsl_sub_5;
    int __gen_e_acsl_f2_7;
    __e_acsl_mpz_t __gen_e_acsl__14;
    __e_acsl_mpz_t __gen_e_acsl_sub_6;
    int __gen_e_acsl_f2_9;
    __gmpz_init_set_si(__gen_e_acsl__12,1L);
    __gmpz_init(__gen_e_acsl_sub_4);
    __gmpz_sub(__gen_e_acsl_sub_4,(__e_acsl_mpz_struct const *)(n),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl__12));
    /*@ assert
        Eva: initialization:
          \initialized((__e_acsl_mpz_struct *)__gen_e_acsl_sub_4);
    */
    __gen_e_acsl_f2_5 = __gen_e_acsl_f2_3((__e_acsl_mpz_struct *)__gen_e_acsl_sub_4);
    __gmpz_init_set_si(__gen_e_acsl__13,2L);
    __gmpz_init(__gen_e_acsl_sub_5);
    __gmpz_sub(__gen_e_acsl_sub_5,(__e_acsl_mpz_struct const *)(n),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl__13));
    /*@ assert
        Eva: initialization:
          \initialized((__e_acsl_mpz_struct *)__gen_e_acsl_sub_5);
    */
    __gen_e_acsl_f2_7 = __gen_e_acsl_f2_3((__e_acsl_mpz_struct *)__gen_e_acsl_sub_5);
    __gmpz_init_set_si(__gen_e_acsl__14,3L);
    __gmpz_init(__gen_e_acsl_sub_6);
    __gmpz_sub(__gen_e_acsl_sub_6,(__e_acsl_mpz_struct const *)(n),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl__14));
    /*@ assert
        Eva: initialization:
          \initialized((__e_acsl_mpz_struct *)__gen_e_acsl_sub_6);
    */
    __gen_e_acsl_f2_9 = __gen_e_acsl_f2_3((__e_acsl_mpz_struct *)__gen_e_acsl_sub_6);
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_5 =
      {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_5,
                                 "__gen_e_acsl_f2_9",0,__gen_e_acsl_f2_9);
    __gen_e_acsl_assert_data_5.blocking = 1;
    __gen_e_acsl_assert_data_5.kind = "RTE";
    __gen_e_acsl_assert_data_5.pred_txt = "__gen_e_acsl_f2_9 != 0";
    __gen_e_acsl_assert_data_5.file = "functions_rec.c";
    __gen_e_acsl_assert_data_5.fct = "f2_3";
    __gen_e_acsl_assert_data_5.line = 13;
    __gen_e_acsl_assert_data_5.name = "division_by_zero";
    __e_acsl_assert(__gen_e_acsl_f2_9 != 0,& __gen_e_acsl_assert_data_5);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_5);
    /*@ assert Eva: division_by_zero: __gen_e_acsl_f2_9 != 0; */
    /*@ assert
        Eva: signed_overflow:
          -2147483648 <= __gen_e_acsl_f2_5 * __gen_e_acsl_f2_7;
    */
    /*@ assert
        Eva: signed_overflow:
          __gen_e_acsl_f2_5 * __gen_e_acsl_f2_7 <= 2147483647;
    */
    /*@ assert
        Eva: signed_overflow:
          (int)(__gen_e_acsl_f2_5 * __gen_e_acsl_f2_7) / __gen_e_acsl_f2_9 <=
          2147483647;
    */
    __gen_e_acsl_if_4 = (__gen_e_acsl_f2_5 * __gen_e_acsl_f2_7) / __gen_e_acsl_f2_9;
    __gmpz_clear(__gen_e_acsl__12);
    __gmpz_clear(__gen_e_acsl_sub_4);
    __gmpz_clear(__gen_e_acsl__13);
    __gmpz_clear(__gen_e_acsl_sub_5);
    __gmpz_clear(__gen_e_acsl__14);
    __gmpz_clear(__gen_e_acsl_sub_6);
  }
  __gmpz_clear(__gen_e_acsl__11);
  return __gen_e_acsl_if_4;
}

/*@ assigns \result;
    assigns \result \from n; */
int __gen_e_acsl_g(int n)
{
  int __retres = 0;
  return __retres;
}

/*@ assigns \result;
    assigns \result \from n; */
int __gen_e_acsl_g_3(long n)
{
  int __retres = 0;
  return __retres;
}

/*@ assigns \result;
    assigns \result \from *((__e_acsl_mpz_struct *)n); */
int __gen_e_acsl_g_5(__e_acsl_mpz_struct * n)
{
  int __retres = 0;
  return __retres;
}

/*@ assigns \result;
    assigns \result \from n; */
int __gen_e_acsl_f3(int n)
{
  int __gen_e_acsl_if_9;
  if (n > 0) {
    int __gen_e_acsl_g_2;
    int __gen_e_acsl_f3_7;
    __gen_e_acsl_g_2 = __gen_e_acsl_g(n);
    __gen_e_acsl_f3_7 = __gen_e_acsl_f3_2(n - 1L);
    __gen_e_acsl_if_9 = __gen_e_acsl_g_2 * __gen_e_acsl_f3_7 - 5;
  }
  else {
    int __gen_e_acsl_g_12;
    __gen_e_acsl_g_12 = __gen_e_acsl_g_3(n + 1L);
    __gen_e_acsl_if_9 = __gen_e_acsl_g_12;
  }
  return __gen_e_acsl_if_9;
}

/*@ assigns \result;
    assigns \result \from n; */
int __gen_e_acsl_f3_2(long n)
{
  int __gen_e_acsl_if_8;
  if (n > 0L) {
    int __gen_e_acsl_g_4;
    __e_acsl_mpz_t __gen_e_acsl_n_4;
    __e_acsl_mpz_t __gen_e_acsl__17;
    __e_acsl_mpz_t __gen_e_acsl_sub_9;
    int __gen_e_acsl_f3_6;
    __gen_e_acsl_g_4 = __gen_e_acsl_g_3(n);
    __gmpz_init_set_si(__gen_e_acsl_n_4,n);
    __gmpz_init_set_si(__gen_e_acsl__17,1L);
    __gmpz_init(__gen_e_acsl_sub_9);
    __gmpz_sub(__gen_e_acsl_sub_9,
               (__e_acsl_mpz_struct const *)(__gen_e_acsl_n_4),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl__17));
    /*@ assert
        Eva: initialization:
          \initialized((__e_acsl_mpz_struct *)__gen_e_acsl_sub_9);
    */
    __gen_e_acsl_f3_6 = __gen_e_acsl_f3_3((__e_acsl_mpz_struct *)__gen_e_acsl_sub_9);
    __gen_e_acsl_if_8 = __gen_e_acsl_g_4 * __gen_e_acsl_f3_6 - 5;
    __gmpz_clear(__gen_e_acsl_n_4);
    __gmpz_clear(__gen_e_acsl__17);
    __gmpz_clear(__gen_e_acsl_sub_9);
  }
  else {
    __e_acsl_mpz_t __gen_e_acsl_n_5;
    __e_acsl_mpz_t __gen_e_acsl__21;
    __e_acsl_mpz_t __gen_e_acsl_add_5;
    int __gen_e_acsl_g_10;
    __gmpz_init_set_si(__gen_e_acsl_n_5,n);
    __gmpz_init_set_si(__gen_e_acsl__21,1L);
    __gmpz_init(__gen_e_acsl_add_5);
    __gmpz_add(__gen_e_acsl_add_5,
               (__e_acsl_mpz_struct const *)(__gen_e_acsl_n_5),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl__21));
    __gen_e_acsl_g_10 = __gen_e_acsl_g_5((__e_acsl_mpz_struct *)__gen_e_acsl_add_5);
    __gen_e_acsl_if_8 = __gen_e_acsl_g_10;
    __gmpz_clear(__gen_e_acsl_n_5);
    __gmpz_clear(__gen_e_acsl__21);
    __gmpz_clear(__gen_e_acsl_add_5);
  }
  return __gen_e_acsl_if_8;
}

/*@ assigns \result;
    assigns \result \from *((__e_acsl_mpz_struct *)n); */
int __gen_e_acsl_f3_3(__e_acsl_mpz_struct * n)
{
  __e_acsl_mpz_t __gen_e_acsl__18;
  int __gen_e_acsl_gt;
  int __gen_e_acsl_if_7;
  __gmpz_init_set_si(__gen_e_acsl__18,0L);
  __gen_e_acsl_gt = __gmpz_cmp((__e_acsl_mpz_struct const *)(n),
                               (__e_acsl_mpz_struct const *)(__gen_e_acsl__18));
  if (__gen_e_acsl_gt > 0) {
    int __gen_e_acsl_g_6;
    __e_acsl_mpz_t __gen_e_acsl__19;
    __e_acsl_mpz_t __gen_e_acsl_sub_10;
    int __gen_e_acsl_f3_5;
    __gen_e_acsl_g_6 = __gen_e_acsl_g_5(n);
    __gmpz_init_set_si(__gen_e_acsl__19,1L);
    __gmpz_init(__gen_e_acsl_sub_10);
    __gmpz_sub(__gen_e_acsl_sub_10,(__e_acsl_mpz_struct const *)(n),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl__19));
    /*@ assert
        Eva: initialization:
          \initialized((__e_acsl_mpz_struct *)__gen_e_acsl_sub_10);
    */
    __gen_e_acsl_f3_5 = __gen_e_acsl_f3_3((__e_acsl_mpz_struct *)__gen_e_acsl_sub_10);
    __gen_e_acsl_if_7 = __gen_e_acsl_g_6 * __gen_e_acsl_f3_5 - 5;
    __gmpz_clear(__gen_e_acsl__19);
    __gmpz_clear(__gen_e_acsl_sub_10);
  }
  else {
    __e_acsl_mpz_t __gen_e_acsl__20;
    __e_acsl_mpz_t __gen_e_acsl_add_4;
    int __gen_e_acsl_g_8;
    __gmpz_init_set_si(__gen_e_acsl__20,1L);
    __gmpz_init(__gen_e_acsl_add_4);
    __gmpz_add(__gen_e_acsl_add_4,(__e_acsl_mpz_struct const *)(n),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl__20));
    /*@ assert
        Eva: initialization:
          \initialized((__e_acsl_mpz_struct *)__gen_e_acsl_add_4);
    */
    __gen_e_acsl_g_8 = __gen_e_acsl_g_5((__e_acsl_mpz_struct *)__gen_e_acsl_add_4);
    __gen_e_acsl_if_7 = __gen_e_acsl_g_8;
    __gmpz_clear(__gen_e_acsl__20);
    __gmpz_clear(__gen_e_acsl_add_4);
  }
  __gmpz_clear(__gen_e_acsl__18);
  return __gen_e_acsl_if_7;
}

/*@ assigns \result;
    assigns \result \from n; */
unsigned long __gen_e_acsl_f4(int n)
{
  unsigned long __gen_e_acsl_if_15;
  if (n < 100) {
    unsigned long __gen_e_acsl_f4_7;
    __gen_e_acsl_f4_7 = __gen_e_acsl_f4_2(n + 1L);
    __gen_e_acsl_if_15 = __gen_e_acsl_f4_7;
  }
  else {
    unsigned long __gen_e_acsl_if_14;
    if ((long)n < 9223372036854775807L) __gen_e_acsl_if_14 = 9223372036854775807UL;
    else __gen_e_acsl_if_14 = 6UL;
    __gen_e_acsl_if_15 = __gen_e_acsl_if_14;
  }
  return __gen_e_acsl_if_15;
}

/*@ assigns \result;
    assigns \result \from n; */
unsigned long __gen_e_acsl_f4_2(long n)
{
  unsigned long __gen_e_acsl_if_13;
  if (n < 100L) {
    __e_acsl_mpz_t __gen_e_acsl_n_6;
    __e_acsl_mpz_t __gen_e_acsl__22;
    __e_acsl_mpz_t __gen_e_acsl_add_6;
    unsigned long __gen_e_acsl_f4_6;
    __gmpz_init_set_si(__gen_e_acsl_n_6,n);
    __gmpz_init_set_si(__gen_e_acsl__22,1L);
    __gmpz_init(__gen_e_acsl_add_6);
    __gmpz_add(__gen_e_acsl_add_6,
               (__e_acsl_mpz_struct const *)(__gen_e_acsl_n_6),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl__22));
    /*@ assert
        Eva: initialization:
          \initialized((__e_acsl_mpz_struct *)__gen_e_acsl_add_6);
    */
    __gen_e_acsl_f4_6 = __gen_e_acsl_f4_3((__e_acsl_mpz_struct *)__gen_e_acsl_add_6);
    __gen_e_acsl_if_13 = __gen_e_acsl_f4_6;
    __gmpz_clear(__gen_e_acsl_n_6);
    __gmpz_clear(__gen_e_acsl__22);
    __gmpz_clear(__gen_e_acsl_add_6);
  }
  else {
    unsigned long __gen_e_acsl_if_12;
    if (n < 9223372036854775807L) __gen_e_acsl_if_12 = 9223372036854775807UL;
    else __gen_e_acsl_if_12 = 6UL;
    __gen_e_acsl_if_13 = __gen_e_acsl_if_12;
  }
  return __gen_e_acsl_if_13;
}

/*@ assigns \result;
    assigns \result \from *((__e_acsl_mpz_struct *)n); */
unsigned long __gen_e_acsl_f4_3(__e_acsl_mpz_struct * n)
{
  __e_acsl_mpz_t __gen_e_acsl__23;
  int __gen_e_acsl_lt_2;
  unsigned long __gen_e_acsl_if_11;
  __gmpz_init_set_si(__gen_e_acsl__23,100L);
  __gen_e_acsl_lt_2 = __gmpz_cmp((__e_acsl_mpz_struct const *)(n),
                                 (__e_acsl_mpz_struct const *)(__gen_e_acsl__23));
  if (__gen_e_acsl_lt_2 < 0) {
    __e_acsl_mpz_t __gen_e_acsl__24;
    __e_acsl_mpz_t __gen_e_acsl_add_7;
    unsigned long __gen_e_acsl_f4_5;
    __gmpz_init_set_si(__gen_e_acsl__24,1L);
    __gmpz_init(__gen_e_acsl_add_7);
    __gmpz_add(__gen_e_acsl_add_7,(__e_acsl_mpz_struct const *)(n),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl__24));
    /*@ assert
        Eva: initialization:
          \initialized((__e_acsl_mpz_struct *)__gen_e_acsl_add_7);
    */
    __gen_e_acsl_f4_5 = __gen_e_acsl_f4_3((__e_acsl_mpz_struct *)__gen_e_acsl_add_7);
    __gen_e_acsl_if_11 = __gen_e_acsl_f4_5;
    __gmpz_clear(__gen_e_acsl__24);
    __gmpz_clear(__gen_e_acsl_add_7);
  }
  else {
    __e_acsl_mpz_t __gen_e_acsl__25;
    int __gen_e_acsl_lt_3;
    unsigned long __gen_e_acsl_if_10;
    __gmpz_init_set_ui(__gen_e_acsl__25,9223372036854775807UL);
    __gen_e_acsl_lt_3 = __gmpz_cmp((__e_acsl_mpz_struct const *)(n),
                                   (__e_acsl_mpz_struct const *)(__gen_e_acsl__25));
    if (__gen_e_acsl_lt_3 < 0) __gen_e_acsl_if_10 = 9223372036854775807UL;
    else __gen_e_acsl_if_10 = 6UL;
    __gen_e_acsl_if_11 = __gen_e_acsl_if_10;
    __gmpz_clear(__gen_e_acsl__25);
  }
  __gmpz_clear(__gen_e_acsl__23);
  return __gen_e_acsl_if_11;
}

/*@ assigns (*__retres_arg)[0];
    assigns (*__retres_arg)[0] \from n; */
void __gen_e_acsl_f5(__e_acsl_mpz_t *__retres_arg, int n)
{
  __e_acsl_mpz_t __gen_e_acsl_if_18;
  if (n >= 0) {
    __e_acsl_mpz_t __gen_e_acsl__26;
    __gmpz_init_set_si(__gen_e_acsl__26,0L);
    __gmpz_init_set(__gen_e_acsl_if_18,
                    (__e_acsl_mpz_struct const *)(__gen_e_acsl__26));
    __gmpz_clear(__gen_e_acsl__26);
  }
  else {
    __e_acsl_mpz_t __gen_e_acsl_f5_7;
    __e_acsl_mpz_t __gen_e_acsl_n_8;
    __e_acsl_mpz_t __gen_e_acsl_add_12;
    __gen_e_acsl_f5_2(& __gen_e_acsl_f5_7,n + 1L);
    __gmpz_init_set_si(__gen_e_acsl_n_8,(long)n);
    __gmpz_init(__gen_e_acsl_add_12);
    __gmpz_add(__gen_e_acsl_add_12,
               (__e_acsl_mpz_struct const *)(__gen_e_acsl_f5_7),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl_n_8));
    __gmpz_init_set(__gen_e_acsl_if_18,
                    (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_12));
    __gmpz_clear(__gen_e_acsl_f5_7);
    __gmpz_clear(__gen_e_acsl_n_8);
    __gmpz_clear(__gen_e_acsl_add_12);
  }
  __gmpz_init_set(*__retres_arg,
                  (__e_acsl_mpz_struct const *)(__gen_e_acsl_if_18));
  __gmpz_clear(__gen_e_acsl_if_18);
  return;
}

/*@ assigns (*__retres_arg)[0];
    assigns (*__retres_arg)[0] \from n; */
void __gen_e_acsl_f5_2(__e_acsl_mpz_t *__retres_arg, long n)
{
  __e_acsl_mpz_t __gen_e_acsl_if_17;
  if (n >= 0L) {
    __e_acsl_mpz_t __gen_e_acsl__27;
    __gmpz_init_set_si(__gen_e_acsl__27,0L);
    __gmpz_init_set(__gen_e_acsl_if_17,
                    (__e_acsl_mpz_struct const *)(__gen_e_acsl__27));
    __gmpz_clear(__gen_e_acsl__27);
  }
  else {
    __e_acsl_mpz_t __gen_e_acsl_n_7;
    __e_acsl_mpz_t __gen_e_acsl__28;
    __e_acsl_mpz_t __gen_e_acsl_add_8;
    __e_acsl_mpz_t __gen_e_acsl_f5_6;
    __e_acsl_mpz_t __gen_e_acsl_add_11;
    __gmpz_init_set_si(__gen_e_acsl_n_7,n);
    __gmpz_init_set_si(__gen_e_acsl__28,1L);
    __gmpz_init(__gen_e_acsl_add_8);
    __gmpz_add(__gen_e_acsl_add_8,
               (__e_acsl_mpz_struct const *)(__gen_e_acsl_n_7),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl__28));
    __gen_e_acsl_f5_3(& __gen_e_acsl_f5_6,
                      (__e_acsl_mpz_struct *)__gen_e_acsl_add_8);
    __gmpz_init(__gen_e_acsl_add_11);
    __gmpz_add(__gen_e_acsl_add_11,
               (__e_acsl_mpz_struct const *)(__gen_e_acsl_f5_6),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl_n_7));
    __gmpz_init_set(__gen_e_acsl_if_17,
                    (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_11));
    __gmpz_clear(__gen_e_acsl_n_7);
    __gmpz_clear(__gen_e_acsl__28);
    __gmpz_clear(__gen_e_acsl_add_8);
    __gmpz_clear(__gen_e_acsl_f5_6);
    __gmpz_clear(__gen_e_acsl_add_11);
  }
  __gmpz_init_set(*__retres_arg,
                  (__e_acsl_mpz_struct const *)(__gen_e_acsl_if_17));
  __gmpz_clear(__gen_e_acsl_if_17);
  return;
}

/*@ assigns (*__retres_arg)[0];
    assigns (*__retres_arg)[0] \from *((__e_acsl_mpz_struct *)n);
 */
void __gen_e_acsl_f5_3(__e_acsl_mpz_t *__retres_arg, __e_acsl_mpz_struct * n)
{
  __e_acsl_mpz_t __gen_e_acsl__29;
  int __gen_e_acsl_ge;
  __e_acsl_mpz_t __gen_e_acsl_if_16;
  __gmpz_init_set_si(__gen_e_acsl__29,0L);
  __gen_e_acsl_ge = __gmpz_cmp((__e_acsl_mpz_struct const *)(n),
                               (__e_acsl_mpz_struct const *)(__gen_e_acsl__29));
  if (__gen_e_acsl_ge >= 0) {
    __e_acsl_mpz_t __gen_e_acsl__30;
    __gmpz_init_set_si(__gen_e_acsl__30,0L);
    __gmpz_init_set(__gen_e_acsl_if_16,
                    (__e_acsl_mpz_struct const *)(__gen_e_acsl__30));
    __gmpz_clear(__gen_e_acsl__30);
  }
  else {
    __e_acsl_mpz_t __gen_e_acsl__31;
    __e_acsl_mpz_t __gen_e_acsl_add_9;
    __e_acsl_mpz_t __gen_e_acsl_f5_5;
    __e_acsl_mpz_t __gen_e_acsl_add_10;
    __gmpz_init_set_si(__gen_e_acsl__31,1L);
    __gmpz_init(__gen_e_acsl_add_9);
    __gmpz_add(__gen_e_acsl_add_9,(__e_acsl_mpz_struct const *)(n),
               (__e_acsl_mpz_struct const *)(__gen_e_acsl__31));
    __gen_e_acsl_f5_3(& __gen_e_acsl_f5_5,
                      (__e_acsl_mpz_struct *)__gen_e_acsl_add_9);
    __gmpz_init(__gen_e_acsl_add_10);
    __gmpz_add(__gen_e_acsl_add_10,
               (__e_acsl_mpz_struct const *)(__gen_e_acsl_f5_5),
               (__e_acsl_mpz_struct const *)(n));
    __gmpz_init_set(__gen_e_acsl_if_16,
                    (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_10));
    __gmpz_clear(__gen_e_acsl__31);
    __gmpz_clear(__gen_e_acsl_add_9);
    __gmpz_clear(__gen_e_acsl_f5_5);
    __gmpz_clear(__gen_e_acsl_add_10);
  }
  __gmpz_init_set(*__retres_arg,
                  (__e_acsl_mpz_struct const *)(__gen_e_acsl_if_16));
  __gmpz_clear(__gen_e_acsl__29);
  __gmpz_clear(__gen_e_acsl_if_16);
  return;
}


