/* Generated by Frama-C */
#include "pthread.h"
#include "sched.h"
#include "signal.h"
#include "stddef.h"
#include "stdint.h"
#include "stdio.h"
#include "time.h"
extern  __attribute__((__FC_BUILTIN__)) int __e_acsl_sound_verdict;

struct mystruct {
   int k ;
   int l ;
};
typedef struct mystruct mystruct;
/*@ predicate p1(int x, int y) = x + y > 0;
 */
int __gen_e_acsl_p1(int x, int y);

/*@ predicate p2(integer x, integer y) = x + y > 0;

*/
int __gen_e_acsl_p2(int x, int y);

int __gen_e_acsl_p2_3(int x, __e_acsl_mpz_struct * y);

/*@ logic integer f1(integer x, integer y) = x + y;

*/
void __gen_e_acsl_f1(__e_acsl_mpz_t *__retres_arg, int x, int y);

void __gen_e_acsl_f1_5(__e_acsl_mpz_t *__retres_arg, int x,
                       __e_acsl_mpz_struct * y);

void __gen_e_acsl_f1_7(__e_acsl_mpz_t *__retres_arg, __e_acsl_mpz_struct * x,
                       __e_acsl_mpz_struct * y);

/*@ logic char h_char(char c) = c;
 */
int __gen_e_acsl_h_char(int c);

/*@ logic short h_short(short s) = s;
 */
int __gen_e_acsl_h_short(int s);

/*@ logic int g_hidden(int x) = x;
 */
int __gen_e_acsl_g_hidden(int x);

/*@ logic int g(int x) = g_hidden(x);
 */
int __gen_e_acsl_g(int x);

/*@ logic mystruct t1(mystruct m) = m;
 */
mystruct __gen_e_acsl_t1(mystruct m);

/*@ logic integer t2(mystruct m) = m.k + m.l;
 */
void __gen_e_acsl_t2(__e_acsl_mpz_t *__retres_arg, mystruct m);

/*@ predicate k_pred(integer x) = x > 0;

*/
int __gen_e_acsl_k_pred(int x);

/*@ requires k_pred(x); */
void __gen_e_acsl_k(int x);

void k(int x)
{
  return;
}

int glob = 5;
/*@ predicate never_called(int x) = x == x;
 */
/*@ logic double f2(double x) = (double)(1 / x);
 */
double __gen_e_acsl_f2(double x);

/*@ predicate p_notyet{L}(integer x) = x > 0;
 */
/*@ logic integer f_notyet{L}(integer x) = x;

*/
int main(void)
{
  int __retres;
  mystruct m;
  __e_acsl_memory_init((int *)0,(char ***)0,8UL);
  int x = 1;
  int y = 2;
  {
    int __gen_e_acsl_p1_2;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data = {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,"y",0,y);
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,"x",0,x);
    __gen_e_acsl_p1_2 = __gen_e_acsl_p1(x,y);
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,"p1(x, y)",0,
                                 __gen_e_acsl_p1_2);
    __gen_e_acsl_assert_data.blocking = 1;
    __gen_e_acsl_assert_data.kind = "Assertion";
    __gen_e_acsl_assert_data.pred_txt = "p1(x, y)";
    __gen_e_acsl_assert_data.file = "functions.c";
    __gen_e_acsl_assert_data.fct = "main";
    __gen_e_acsl_assert_data.line = 44;
    __e_acsl_assert(__gen_e_acsl_p1_2,& __gen_e_acsl_assert_data);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data);
  }
  /*@ assert p1(x, y); */ ;
  {
    int __gen_e_acsl_p2_2;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_2 =
      {.values = (void *)0};
    __gen_e_acsl_p2_2 = __gen_e_acsl_p2(3,4);
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_2,"p2(3, 4)",0,
                                 __gen_e_acsl_p2_2);
    __gen_e_acsl_assert_data_2.blocking = 1;
    __gen_e_acsl_assert_data_2.kind = "Assertion";
    __gen_e_acsl_assert_data_2.pred_txt = "p2(3, 4)";
    __gen_e_acsl_assert_data_2.file = "functions.c";
    __gen_e_acsl_assert_data_2.fct = "main";
    __gen_e_acsl_assert_data_2.line = 45;
    __e_acsl_assert(__gen_e_acsl_p2_2,& __gen_e_acsl_assert_data_2);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_2);
  }
  /*@ assert p2(3, 4); */ ;
  {
    __e_acsl_mpz_t __gen_e_acsl__3;
    int __gen_e_acsl_p2_4;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_3 =
      {.values = (void *)0};
    __gmpz_init_set_str(__gen_e_acsl__3,"99999999999999999999999999999",10);
    __gen_e_acsl_p2_4 = __gen_e_acsl_p2_3(5,
                                          (__e_acsl_mpz_struct *)__gen_e_acsl__3);
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_3,
                                 "p2(5, 99999999999999999999999999999)",0,
                                 __gen_e_acsl_p2_4);
    __gen_e_acsl_assert_data_3.blocking = 1;
    __gen_e_acsl_assert_data_3.kind = "Assertion";
    __gen_e_acsl_assert_data_3.pred_txt = "p2(5, 99999999999999999999999999999)";
    __gen_e_acsl_assert_data_3.file = "functions.c";
    __gen_e_acsl_assert_data_3.fct = "main";
    __gen_e_acsl_assert_data_3.line = 46;
    __e_acsl_assert(__gen_e_acsl_p2_4,& __gen_e_acsl_assert_data_3);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_3);
    __gmpz_clear(__gen_e_acsl__3);
  }
  /*@ assert p2(5, 99999999999999999999999999999); */ ;
  {
    __e_acsl_mpz_t __gen_e_acsl_f1_2;
    __e_acsl_mpz_t __gen_e_acsl__5;
    int __gen_e_acsl_eq;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_4 =
      {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_4,"y",0,y);
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_4,"x",0,x);
    __gen_e_acsl_f1(& __gen_e_acsl_f1_2,x,y);
    __e_acsl_assert_register_mpz(& __gen_e_acsl_assert_data_4,"f1(x, y)",0,
                                 (__e_acsl_mpz_struct const *)(__gen_e_acsl_f1_2));
    __gmpz_init_set_si(__gen_e_acsl__5,3L);
    __gen_e_acsl_eq = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_f1_2),
                                 (__e_acsl_mpz_struct const *)(__gen_e_acsl__5));
    __gen_e_acsl_assert_data_4.blocking = 1;
    __gen_e_acsl_assert_data_4.kind = "Assertion";
    __gen_e_acsl_assert_data_4.pred_txt = "f1(x, y) == 3";
    __gen_e_acsl_assert_data_4.file = "functions.c";
    __gen_e_acsl_assert_data_4.fct = "main";
    __gen_e_acsl_assert_data_4.line = 48;
    __e_acsl_assert(__gen_e_acsl_eq == 0,& __gen_e_acsl_assert_data_4);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_4);
    __gmpz_clear(__gen_e_acsl_f1_2);
    __gmpz_clear(__gen_e_acsl__5);
  }
  /*@ assert f1(x, y) == 3; */ ;
  {
    __e_acsl_mpz_t __gen_e_acsl_f1_4;
    int __gen_e_acsl_p2_6;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_5 =
      {.values = (void *)0};
    __gen_e_acsl_f1(& __gen_e_acsl_f1_4,3,4);
    __e_acsl_assert_register_mpz(& __gen_e_acsl_assert_data_5,"f1(3, 4)",0,
                                 (__e_acsl_mpz_struct const *)(__gen_e_acsl_f1_4));
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_5,"x",0,x);
    /*@ assert
        Eva: initialization:
          \initialized((__e_acsl_mpz_struct *)__gen_e_acsl_f1_4);
    */
    __gen_e_acsl_p2_6 = __gen_e_acsl_p2_3(x,
                                          (__e_acsl_mpz_struct *)__gen_e_acsl_f1_4);
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_5,
                                 "p2(x, f1(3, 4))",0,__gen_e_acsl_p2_6);
    __gen_e_acsl_assert_data_5.blocking = 1;
    __gen_e_acsl_assert_data_5.kind = "Assertion";
    __gen_e_acsl_assert_data_5.pred_txt = "p2(x, f1(3, 4))";
    __gen_e_acsl_assert_data_5.file = "functions.c";
    __gen_e_acsl_assert_data_5.fct = "main";
    __gen_e_acsl_assert_data_5.line = 49;
    __e_acsl_assert(__gen_e_acsl_p2_6,& __gen_e_acsl_assert_data_5);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_5);
    __gmpz_clear(__gen_e_acsl_f1_4);
  }
  /*@ assert p2(x, f1(3, 4)); */ ;
  {
    __e_acsl_mpz_t __gen_e_acsl__6;
    __e_acsl_mpz_t __gen_e_acsl_f1_6;
    __e_acsl_mpz_t __gen_e_acsl__7;
    int __gen_e_acsl_gt_4;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_6 =
      {.values = (void *)0};
    __gmpz_init_set_str(__gen_e_acsl__6,"99999999999999999999999999999",10);
    __gen_e_acsl_f1_5(& __gen_e_acsl_f1_6,9,
                      (__e_acsl_mpz_struct *)__gen_e_acsl__6);
    __e_acsl_assert_register_mpz(& __gen_e_acsl_assert_data_6,
                                 "f1(9, 99999999999999999999999999999)",0,
                                 (__e_acsl_mpz_struct const *)(__gen_e_acsl_f1_6));
    __gmpz_init_set_si(__gen_e_acsl__7,0L);
    __gen_e_acsl_gt_4 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_f1_6),
                                   (__e_acsl_mpz_struct const *)(__gen_e_acsl__7));
    __gen_e_acsl_assert_data_6.blocking = 1;
    __gen_e_acsl_assert_data_6.kind = "Assertion";
    __gen_e_acsl_assert_data_6.pred_txt = "f1(9, 99999999999999999999999999999) > 0";
    __gen_e_acsl_assert_data_6.file = "functions.c";
    __gen_e_acsl_assert_data_6.fct = "main";
    __gen_e_acsl_assert_data_6.line = 50;
    __e_acsl_assert(__gen_e_acsl_gt_4 > 0,& __gen_e_acsl_assert_data_6);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_6);
    __gmpz_clear(__gen_e_acsl__6);
    __gmpz_clear(__gen_e_acsl_f1_6);
    __gmpz_clear(__gen_e_acsl__7);
  }
  /*@ assert f1(9, 99999999999999999999999999999) > 0; */ ;
  {
    __e_acsl_mpz_t __gen_e_acsl__8;
    __e_acsl_mpz_t __gen_e_acsl_f1_8;
    __e_acsl_mpz_t __gen_e_acsl__9;
    int __gen_e_acsl_eq_2;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_7 =
      {.values = (void *)0};
    __gmpz_init_set_str(__gen_e_acsl__8,"99999999999999999999999999999",10);
    __gen_e_acsl_f1_7(& __gen_e_acsl_f1_8,
                      (__e_acsl_mpz_struct *)__gen_e_acsl__8,
                      (__e_acsl_mpz_struct *)__gen_e_acsl__8);
    __e_acsl_assert_register_mpz(& __gen_e_acsl_assert_data_7,
                                 "f1(99999999999999999999999999999, 99999999999999999999999999999)",
                                 0,
                                 (__e_acsl_mpz_struct const *)(__gen_e_acsl_f1_8));
    __gmpz_init_set_str(__gen_e_acsl__9,"199999999999999999999999999998",10);
    __gen_e_acsl_eq_2 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_f1_8),
                                   (__e_acsl_mpz_struct const *)(__gen_e_acsl__9));
    __gen_e_acsl_assert_data_7.blocking = 1;
    __gen_e_acsl_assert_data_7.kind = "Assertion";
    __gen_e_acsl_assert_data_7.pred_txt = "f1(99999999999999999999999999999, 99999999999999999999999999999) ==\n199999999999999999999999999998";
    __gen_e_acsl_assert_data_7.file = "functions.c";
    __gen_e_acsl_assert_data_7.fct = "main";
    __gen_e_acsl_assert_data_7.line = 51;
    __e_acsl_assert(__gen_e_acsl_eq_2 == 0,& __gen_e_acsl_assert_data_7);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_7);
    __gmpz_clear(__gen_e_acsl__8);
    __gmpz_clear(__gen_e_acsl_f1_8);
    __gmpz_clear(__gen_e_acsl__9);
  }
  /*@
  assert
  f1(99999999999999999999999999999, 99999999999999999999999999999) ==
  199999999999999999999999999998; */
  ;
  {
    int __gen_e_acsl_g_2;
    __e_acsl_mpz_t __gen_e_acsl_app;
    __e_acsl_mpz_t __gen_e_acsl_x_6;
    int __gen_e_acsl_eq_3;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_8 =
      {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_8,"x",0,x);
    __gen_e_acsl_g_2 = __gen_e_acsl_g(x);
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_8,"g(x)",0,
                                 __gen_e_acsl_g_2);
    __gmpz_init_set_si(__gen_e_acsl_app,(long)__gen_e_acsl_g_2);
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_8,"x",0,x);
    __gmpz_init_set_si(__gen_e_acsl_x_6,(long)x);
    __gen_e_acsl_eq_3 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_app),
                                   (__e_acsl_mpz_struct const *)(__gen_e_acsl_x_6));
    __gen_e_acsl_assert_data_8.blocking = 1;
    __gen_e_acsl_assert_data_8.kind = "Assertion";
    __gen_e_acsl_assert_data_8.pred_txt = "g(x) == x";
    __gen_e_acsl_assert_data_8.file = "functions.c";
    __gen_e_acsl_assert_data_8.fct = "main";
    __gen_e_acsl_assert_data_8.line = 56;
    __e_acsl_assert(__gen_e_acsl_eq_3 == 0,& __gen_e_acsl_assert_data_8);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_8);
    __gmpz_clear(__gen_e_acsl_app);
    __gmpz_clear(__gen_e_acsl_x_6);
  }
  /*@ assert g(x) == x; */ ;
  char c = (char)'c';
  {
    int __gen_e_acsl_h_char_2;
    __e_acsl_mpz_t __gen_e_acsl_app_2;
    __e_acsl_mpz_t __gen_e_acsl_c;
    int __gen_e_acsl_eq_4;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_9 =
      {.values = (void *)0};
    __e_acsl_assert_register_char(& __gen_e_acsl_assert_data_9,"c",0,c);
    __gen_e_acsl_h_char_2 = __gen_e_acsl_h_char((int)c);
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_9,"h_char(c)",0,
                                 __gen_e_acsl_h_char_2);
    __gmpz_init_set_si(__gen_e_acsl_app_2,(long)__gen_e_acsl_h_char_2);
    __e_acsl_assert_register_char(& __gen_e_acsl_assert_data_9,"c",0,c);
    __gmpz_init_set_si(__gen_e_acsl_c,(long)c);
    __gen_e_acsl_eq_4 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_app_2),
                                   (__e_acsl_mpz_struct const *)(__gen_e_acsl_c));
    __gen_e_acsl_assert_data_9.blocking = 1;
    __gen_e_acsl_assert_data_9.kind = "Assertion";
    __gen_e_acsl_assert_data_9.pred_txt = "h_char(c) == c";
    __gen_e_acsl_assert_data_9.file = "functions.c";
    __gen_e_acsl_assert_data_9.fct = "main";
    __gen_e_acsl_assert_data_9.line = 59;
    __e_acsl_assert(__gen_e_acsl_eq_4 == 0,& __gen_e_acsl_assert_data_9);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_9);
    __gmpz_clear(__gen_e_acsl_app_2);
    __gmpz_clear(__gen_e_acsl_c);
  }
  /*@ assert h_char(c) == c; */ ;
  short s = (short)1;
  {
    int __gen_e_acsl_h_short_2;
    __e_acsl_mpz_t __gen_e_acsl_app_3;
    __e_acsl_mpz_t __gen_e_acsl_s;
    int __gen_e_acsl_eq_5;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_10 =
      {.values = (void *)0};
    __e_acsl_assert_register_short(& __gen_e_acsl_assert_data_10,"s",0,s);
    __gen_e_acsl_h_short_2 = __gen_e_acsl_h_short((int)s);
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_10,"h_short(s)",
                                 0,__gen_e_acsl_h_short_2);
    __gmpz_init_set_si(__gen_e_acsl_app_3,(long)__gen_e_acsl_h_short_2);
    __e_acsl_assert_register_short(& __gen_e_acsl_assert_data_10,"s",0,s);
    __gmpz_init_set_si(__gen_e_acsl_s,(long)s);
    __gen_e_acsl_eq_5 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_app_3),
                                   (__e_acsl_mpz_struct const *)(__gen_e_acsl_s));
    __gen_e_acsl_assert_data_10.blocking = 1;
    __gen_e_acsl_assert_data_10.kind = "Assertion";
    __gen_e_acsl_assert_data_10.pred_txt = "h_short(s) == s";
    __gen_e_acsl_assert_data_10.file = "functions.c";
    __gen_e_acsl_assert_data_10.fct = "main";
    __gen_e_acsl_assert_data_10.line = 61;
    __e_acsl_assert(__gen_e_acsl_eq_5 == 0,& __gen_e_acsl_assert_data_10);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_10);
    __gmpz_clear(__gen_e_acsl_app_3);
    __gmpz_clear(__gen_e_acsl_s);
  }
  /*@ assert h_short(s) == s; */ ;
  m.k = 8;
  m.l = 9;
  {
    mystruct __gen_e_acsl_t1_2;
    __e_acsl_mpz_t __gen_e_acsl_t2_2;
    __e_acsl_mpz_t __gen_e_acsl__12;
    int __gen_e_acsl_eq_6;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_11 =
      {.values = (void *)0};
    __e_acsl_assert_register_struct(& __gen_e_acsl_assert_data_11,"m");
    __gen_e_acsl_t1_2 = __gen_e_acsl_t1(m);
    __e_acsl_assert_register_struct(& __gen_e_acsl_assert_data_11,"t1(m)");
    __gen_e_acsl_t2(& __gen_e_acsl_t2_2,__gen_e_acsl_t1_2);
    __e_acsl_assert_register_mpz(& __gen_e_acsl_assert_data_11,"t2(t1(m))",0,
                                 (__e_acsl_mpz_struct const *)(__gen_e_acsl_t2_2));
    __gmpz_init_set_si(__gen_e_acsl__12,17L);
    __gen_e_acsl_eq_6 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_t2_2),
                                   (__e_acsl_mpz_struct const *)(__gen_e_acsl__12));
    __gen_e_acsl_assert_data_11.blocking = 1;
    __gen_e_acsl_assert_data_11.kind = "Assertion";
    __gen_e_acsl_assert_data_11.pred_txt = "t2(t1(m)) == 17";
    __gen_e_acsl_assert_data_11.file = "functions.c";
    __gen_e_acsl_assert_data_11.fct = "main";
    __gen_e_acsl_assert_data_11.line = 66;
    __e_acsl_assert(__gen_e_acsl_eq_6 == 0,& __gen_e_acsl_assert_data_11);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_11);
    __gmpz_clear(__gen_e_acsl_t2_2);
    __gmpz_clear(__gen_e_acsl__12);
  }
  /*@ assert t2(t1(m)) == 17; */ ;
  __gen_e_acsl_k(9);
  double d = 2.0;
  {
    double __gen_e_acsl_f2_2;
    __e_acsl_mpq_t __gen_e_acsl__15;
    __e_acsl_mpq_t __gen_e_acsl__16;
    int __gen_e_acsl_gt_5;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_12 =
      {.values = (void *)0};
    __e_acsl_assert_register_double(& __gen_e_acsl_assert_data_12,"d",d);
    __gen_e_acsl_f2_2 = __gen_e_acsl_f2(d);
    __e_acsl_assert_register_double(& __gen_e_acsl_assert_data_12,"f2(d)",
                                    __gen_e_acsl_f2_2);
    __gmpq_init(__gen_e_acsl__15);
    __gmpq_set_str(__gen_e_acsl__15,"0",10);
    __gmpq_init(__gen_e_acsl__16);
    __gmpq_set_d(__gen_e_acsl__16,__gen_e_acsl_f2_2);
    __gen_e_acsl_gt_5 = __gmpq_cmp((__e_acsl_mpq_struct const *)(__gen_e_acsl__16),
                                   (__e_acsl_mpq_struct const *)(__gen_e_acsl__15));
    __gen_e_acsl_assert_data_12.blocking = 1;
    __gen_e_acsl_assert_data_12.kind = "Assertion";
    __gen_e_acsl_assert_data_12.pred_txt = "f2(d) > 0";
    __gen_e_acsl_assert_data_12.file = "functions.c";
    __gen_e_acsl_assert_data_12.fct = "main";
    __gen_e_acsl_assert_data_12.line = 71;
    __e_acsl_assert(__gen_e_acsl_gt_5 > 0,& __gen_e_acsl_assert_data_12);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_12);
    __gmpq_clear(__gen_e_acsl__15);
    __gmpq_clear(__gen_e_acsl__16);
  }
  /*@ assert f2(d) > 0; */ ;
  __retres = 0;
  __e_acsl_memory_clean();
  return __retres;
}

/*@ requires k_pred(x); */
void __gen_e_acsl_k(int x)
{
  {
    int __gen_e_acsl_k_pred_2;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data = {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,"x",0,x);
    __gen_e_acsl_k_pred_2 = __gen_e_acsl_k_pred(x);
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,"k_pred(x)",0,
                                 __gen_e_acsl_k_pred_2);
    __gen_e_acsl_assert_data.blocking = 1;
    __gen_e_acsl_assert_data.kind = "Precondition";
    __gen_e_acsl_assert_data.pred_txt = "k_pred(x)";
    __gen_e_acsl_assert_data.file = "functions.c";
    __gen_e_acsl_assert_data.fct = "k";
    __gen_e_acsl_assert_data.line = 27;
    __e_acsl_assert(__gen_e_acsl_k_pred_2,& __gen_e_acsl_assert_data);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data);
  }
  k(x);
  return;
}

/*@ assigns \result;
    assigns \result \from x, y; */
int __gen_e_acsl_p1(int x, int y)
{
  __e_acsl_mpz_t __gen_e_acsl_x;
  __e_acsl_mpz_t __gen_e_acsl_y;
  __e_acsl_mpz_t __gen_e_acsl_add;
  __e_acsl_mpz_t __gen_e_acsl_;
  int __gen_e_acsl_gt;
  __gmpz_init_set_si(__gen_e_acsl_x,(long)x);
  __gmpz_init_set_si(__gen_e_acsl_y,(long)y);
  __gmpz_init(__gen_e_acsl_add);
  __gmpz_add(__gen_e_acsl_add,(__e_acsl_mpz_struct const *)(__gen_e_acsl_x),
             (__e_acsl_mpz_struct const *)(__gen_e_acsl_y));
  __gmpz_init_set_si(__gen_e_acsl_,0L);
  __gen_e_acsl_gt = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_add),
                               (__e_acsl_mpz_struct const *)(__gen_e_acsl_));
  int __retres = __gen_e_acsl_gt > 0;
  __gmpz_clear(__gen_e_acsl_x);
  __gmpz_clear(__gen_e_acsl_y);
  __gmpz_clear(__gen_e_acsl_add);
  __gmpz_clear(__gen_e_acsl_);
  return __retres;
}

/*@ assigns \result;
    assigns \result \from x, y; */
int __gen_e_acsl_p2(int x, int y)
{
  __e_acsl_mpz_t __gen_e_acsl_x_2;
  __e_acsl_mpz_t __gen_e_acsl_y_2;
  __e_acsl_mpz_t __gen_e_acsl_add_2;
  __e_acsl_mpz_t __gen_e_acsl__2;
  int __gen_e_acsl_gt_2;
  __gmpz_init_set_si(__gen_e_acsl_x_2,(long)x);
  __gmpz_init_set_si(__gen_e_acsl_y_2,(long)y);
  __gmpz_init(__gen_e_acsl_add_2);
  __gmpz_add(__gen_e_acsl_add_2,
             (__e_acsl_mpz_struct const *)(__gen_e_acsl_x_2),
             (__e_acsl_mpz_struct const *)(__gen_e_acsl_y_2));
  __gmpz_init_set_si(__gen_e_acsl__2,0L);
  __gen_e_acsl_gt_2 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_add_2),
                                 (__e_acsl_mpz_struct const *)(__gen_e_acsl__2));
  int __retres = __gen_e_acsl_gt_2 > 0;
  __gmpz_clear(__gen_e_acsl_x_2);
  __gmpz_clear(__gen_e_acsl_y_2);
  __gmpz_clear(__gen_e_acsl_add_2);
  __gmpz_clear(__gen_e_acsl__2);
  return __retres;
}

/*@ assigns \result;
    assigns \result \from x, *((__e_acsl_mpz_struct *)y); */
int __gen_e_acsl_p2_3(int x, __e_acsl_mpz_struct * y)
{
  __e_acsl_mpz_t __gen_e_acsl_x_3;
  __e_acsl_mpz_t __gen_e_acsl_add_3;
  __e_acsl_mpz_t __gen_e_acsl__4;
  int __gen_e_acsl_gt_3;
  __gmpz_init_set_si(__gen_e_acsl_x_3,(long)x);
  __gmpz_init(__gen_e_acsl_add_3);
  __gmpz_add(__gen_e_acsl_add_3,
             (__e_acsl_mpz_struct const *)(__gen_e_acsl_x_3),
             (__e_acsl_mpz_struct const *)(y));
  __gmpz_init_set_si(__gen_e_acsl__4,0L);
  __gen_e_acsl_gt_3 = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_add_3),
                                 (__e_acsl_mpz_struct const *)(__gen_e_acsl__4));
  int __retres = __gen_e_acsl_gt_3 > 0;
  __gmpz_clear(__gen_e_acsl_x_3);
  __gmpz_clear(__gen_e_acsl_add_3);
  __gmpz_clear(__gen_e_acsl__4);
  return __retres;
}

/*@ assigns (*__retres_arg)[0];
    assigns (*__retres_arg)[0] \from x, y; */
void __gen_e_acsl_f1(__e_acsl_mpz_t *__retres_arg, int x, int y)
{
  __e_acsl_mpz_t __gen_e_acsl_x_4;
  __e_acsl_mpz_t __gen_e_acsl_y_3;
  __e_acsl_mpz_t __gen_e_acsl_add_4;
  __gmpz_init_set_si(__gen_e_acsl_x_4,(long)x);
  __gmpz_init_set_si(__gen_e_acsl_y_3,(long)y);
  __gmpz_init(__gen_e_acsl_add_4);
  __gmpz_add(__gen_e_acsl_add_4,
             (__e_acsl_mpz_struct const *)(__gen_e_acsl_x_4),
             (__e_acsl_mpz_struct const *)(__gen_e_acsl_y_3));
  __gmpz_init_set(*__retres_arg,
                  (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_4));
  __gmpz_clear(__gen_e_acsl_x_4);
  __gmpz_clear(__gen_e_acsl_y_3);
  __gmpz_clear(__gen_e_acsl_add_4);
  return;
}

/*@ assigns (*__retres_arg)[0];
    assigns (*__retres_arg)[0] \from x, *((__e_acsl_mpz_struct *)y);
 */
void __gen_e_acsl_f1_5(__e_acsl_mpz_t *__retres_arg, int x,
                       __e_acsl_mpz_struct * y)
{
  __e_acsl_mpz_t __gen_e_acsl_x_5;
  __e_acsl_mpz_t __gen_e_acsl_add_5;
  __gmpz_init_set_si(__gen_e_acsl_x_5,(long)x);
  __gmpz_init(__gen_e_acsl_add_5);
  __gmpz_add(__gen_e_acsl_add_5,
             (__e_acsl_mpz_struct const *)(__gen_e_acsl_x_5),
             (__e_acsl_mpz_struct const *)(y));
  __gmpz_init_set(*__retres_arg,
                  (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_5));
  __gmpz_clear(__gen_e_acsl_x_5);
  __gmpz_clear(__gen_e_acsl_add_5);
  return;
}

/*@ assigns (*__retres_arg)[0];
    assigns (*__retres_arg)[0]
      \from *((__e_acsl_mpz_struct *)x), *((__e_acsl_mpz_struct *)y);
 */
void __gen_e_acsl_f1_7(__e_acsl_mpz_t *__retres_arg, __e_acsl_mpz_struct * x,
                       __e_acsl_mpz_struct * y)
{
  __e_acsl_mpz_t __gen_e_acsl_add_6;
  __gmpz_init(__gen_e_acsl_add_6);
  __gmpz_add(__gen_e_acsl_add_6,(__e_acsl_mpz_struct const *)(x),
             (__e_acsl_mpz_struct const *)(y));
  __gmpz_init_set(*__retres_arg,
                  (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_6));
  __gmpz_clear(__gen_e_acsl_add_6);
  return;
}

/*@ assigns \result;
    assigns \result \from c; */
int __gen_e_acsl_h_char(int c)
{
  return c;
}

/*@ assigns \result;
    assigns \result \from s; */
int __gen_e_acsl_h_short(int s)
{
  return s;
}

/*@ assigns \result;
    assigns \result \from x; */
int __gen_e_acsl_g_hidden(int x)
{
  return x;
}

/*@ assigns \result;
    assigns \result \from x; */
int __gen_e_acsl_g(int x)
{
  int __gen_e_acsl_g_hidden_2;
  __gen_e_acsl_g_hidden_2 = __gen_e_acsl_g_hidden(x);
  return __gen_e_acsl_g_hidden_2;
}

/*@ assigns \result;
    assigns \result \from m; */
mystruct __gen_e_acsl_t1(mystruct m)
{
  return m;
}

/*@ assigns (*__retres_arg)[0];
    assigns (*__retres_arg)[0] \from m; */
void __gen_e_acsl_t2(__e_acsl_mpz_t *__retres_arg, mystruct m)
{
  __e_acsl_mpz_t __gen_e_acsl__10;
  __e_acsl_mpz_t __gen_e_acsl__11;
  __e_acsl_mpz_t __gen_e_acsl_add_7;
  __gmpz_init_set_si(__gen_e_acsl__10,(long)m.k);
  __gmpz_init_set_si(__gen_e_acsl__11,(long)m.l);
  __gmpz_init(__gen_e_acsl_add_7);
  __gmpz_add(__gen_e_acsl_add_7,
             (__e_acsl_mpz_struct const *)(__gen_e_acsl__10),
             (__e_acsl_mpz_struct const *)(__gen_e_acsl__11));
  __gmpz_init_set(*__retres_arg,
                  (__e_acsl_mpz_struct const *)(__gen_e_acsl_add_7));
  __gmpz_clear(__gen_e_acsl__10);
  __gmpz_clear(__gen_e_acsl__11);
  __gmpz_clear(__gen_e_acsl_add_7);
  return;
}

/*@ assigns \result;
    assigns \result \from x; */
int __gen_e_acsl_k_pred(int x)
{
  __e_acsl_mpz_t __gen_e_acsl_x;
  __e_acsl_mpz_t __gen_e_acsl_;
  int __gen_e_acsl_gt;
  __gmpz_init_set_si(__gen_e_acsl_x,(long)x);
  __gmpz_init_set_si(__gen_e_acsl_,0L);
  __gen_e_acsl_gt = __gmpz_cmp((__e_acsl_mpz_struct const *)(__gen_e_acsl_x),
                               (__e_acsl_mpz_struct const *)(__gen_e_acsl_));
  int __retres = __gen_e_acsl_gt > 0;
  __gmpz_clear(__gen_e_acsl_x);
  __gmpz_clear(__gen_e_acsl_);
  return __retres;
}

/*@ assigns \result;
    assigns \result \from x; */
double __gen_e_acsl_f2(double x)
{
  __e_acsl_mpq_t __gen_e_acsl__13;
  __e_acsl_mpq_t __gen_e_acsl__14;
  __e_acsl_mpq_t __gen_e_acsl_div;
  double __gen_e_acsl_cast;
  __gmpq_init(__gen_e_acsl__13);
  __gmpq_set_str(__gen_e_acsl__13,"1",10);
  __gmpq_init(__gen_e_acsl__14);
  __gmpq_set_d(__gen_e_acsl__14,x);
  __gmpq_init(__gen_e_acsl_div);
  __gmpq_div(__gen_e_acsl_div,
             (__e_acsl_mpq_struct const *)(__gen_e_acsl__13),
             (__e_acsl_mpq_struct const *)(__gen_e_acsl__14));
  __gen_e_acsl_cast = __gmpq_get_d((__e_acsl_mpq_struct const *)(__gen_e_acsl_div));
  __gmpq_clear(__gen_e_acsl__13);
  __gmpq_clear(__gen_e_acsl__14);
  __gmpq_clear(__gen_e_acsl_div);
  /*@ assert Eva: is_nan_or_infinite: \is_finite(__gen_e_acsl_cast); */
  return __gen_e_acsl_cast;
}


