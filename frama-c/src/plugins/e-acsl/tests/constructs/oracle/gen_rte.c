/* Generated by Frama-C */
#include "pthread.h"
#include "sched.h"
#include "signal.h"
#include "stddef.h"
#include "stdint.h"
#include "stdio.h"
#include "time.h"
extern  __attribute__((__FC_BUILTIN__)) int __e_acsl_sound_verdict;

/*@ requires 1 % a == 1;
    ensures 1 % \old(b) == 1;
    
    behavior bhvr:
      assumes 1 % c == 1;
      requires 1 % d == 1;
      requires 1 % f == 1 || 1 % g == 1;
      requires 1 % h == 1 && 1 % i == 1;
      requires \let var = 1; var % j == 1;
      requires \forall integer var; 0 <= var < k ==> var % k == var;
      requires \exists integer var; 0 <= var < l && var % l == var;
      ensures 1 % \old(e) == 1;
 */
void __gen_e_acsl_test(int a, int b, int c, int d, int e, int f, int g,
                       int h, int i, int j, int k, int l);

void test(int a, int b, int c, int d, int e, int f, int g, int h, int i,
          int j, int k, int l)
{
  return;
}

int main(void)
{
  int __retres;
  __e_acsl_memory_init((int *)0,(char ***)0,8UL);
  __gen_e_acsl_test(2,3,4,5,6,7,8,9,10,11,12,13);
  __retres = 0;
  __e_acsl_memory_clean();
  return __retres;
}

/*@ requires 1 % a == 1;
    ensures 1 % \old(b) == 1;
    
    behavior bhvr:
      assumes 1 % c == 1;
      requires 1 % d == 1;
      requires 1 % f == 1 || 1 % g == 1;
      requires 1 % h == 1 && 1 % i == 1;
      requires \let var = 1; var % j == 1;
      requires \forall integer var; 0 <= var < k ==> var % k == var;
      requires \exists integer var; 0 <= var < l && var % l == var;
      ensures 1 % \old(e) == 1;
 */
void __gen_e_acsl_test(int a, int b, int c, int d, int e, int f, int g,
                       int h, int i, int j, int k, int l)
{
  __e_acsl_contract_t *__gen_e_acsl_contract;
  int __gen_e_acsl_at_2;
  int __gen_e_acsl_at;
  {
    int __gen_e_acsl_assumes_value;
    __gen_e_acsl_at = b;
    __gen_e_acsl_at_2 = e;
    __gen_e_acsl_contract = __e_acsl_contract_init(1UL);
    __e_acsl_assert_data_t __gen_e_acsl_assert_data = {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,"a",0,a);
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_2 =
      {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_2,"a",0,a);
    __gen_e_acsl_assert_data_2.blocking = 1;
    __gen_e_acsl_assert_data_2.kind = "RTE";
    __gen_e_acsl_assert_data_2.pred_txt = "a != 0";
    __gen_e_acsl_assert_data_2.file = "rte.i";
    __gen_e_acsl_assert_data_2.fct = "test";
    __gen_e_acsl_assert_data_2.line = 7;
    __gen_e_acsl_assert_data_2.name = "division_by_zero";
    __e_acsl_assert(a != 0,& __gen_e_acsl_assert_data_2);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_2);
    __gen_e_acsl_assert_data.blocking = 1;
    __gen_e_acsl_assert_data.kind = "Precondition";
    __gen_e_acsl_assert_data.pred_txt = "1 % a == 1";
    __gen_e_acsl_assert_data.file = "rte.i";
    __gen_e_acsl_assert_data.fct = "test";
    __gen_e_acsl_assert_data.line = 7;
    __e_acsl_assert(1 % a == 1,& __gen_e_acsl_assert_data);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data);
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_3 =
      {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_3,"c",0,c);
    __gen_e_acsl_assert_data_3.blocking = 1;
    __gen_e_acsl_assert_data_3.kind = "RTE";
    __gen_e_acsl_assert_data_3.pred_txt = "c != 0";
    __gen_e_acsl_assert_data_3.file = "rte.i";
    __gen_e_acsl_assert_data_3.fct = "test";
    __gen_e_acsl_assert_data_3.line = 11;
    __gen_e_acsl_assert_data_3.name = "division_by_zero";
    __e_acsl_assert(c != 0,& __gen_e_acsl_assert_data_3);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_3);
    __e_acsl_contract_set_behavior_assumes(__gen_e_acsl_contract,0UL,
                                           1 % c == 1);
    __gen_e_acsl_assumes_value = __e_acsl_contract_get_behavior_assumes
    ((__e_acsl_contract_t const *)__gen_e_acsl_contract,0UL);
    if (__gen_e_acsl_assumes_value) {
      int __gen_e_acsl_or;
      int __gen_e_acsl_and;
      int __gen_e_acsl_var;
      int __gen_e_acsl_forall;
      int __gen_e_acsl_var_2;
      int __gen_e_acsl_exists;
      int __gen_e_acsl_var_3;
      __e_acsl_assert_data_t __gen_e_acsl_assert_data_4 =
        {.values = (void *)0};
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_4,"d",0,d);
      __e_acsl_assert_data_t __gen_e_acsl_assert_data_5 =
        {.values = (void *)0};
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_5,"d",0,d);
      __gen_e_acsl_assert_data_5.blocking = 1;
      __gen_e_acsl_assert_data_5.kind = "RTE";
      __gen_e_acsl_assert_data_5.pred_txt = "d != 0";
      __gen_e_acsl_assert_data_5.file = "rte.i";
      __gen_e_acsl_assert_data_5.fct = "test";
      __gen_e_acsl_assert_data_5.line = 12;
      __gen_e_acsl_assert_data_5.name = "division_by_zero";
      __e_acsl_assert(d != 0,& __gen_e_acsl_assert_data_5);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data_5);
      __e_acsl_assert_data_t __gen_e_acsl_assert_data_6 =
        {.values = (void *)0};
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_6,"f",0,f);
      __e_acsl_assert_data_t __gen_e_acsl_assert_data_7 =
        {.values = (void *)0};
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_7,"f",0,f);
      __gen_e_acsl_assert_data_7.blocking = 1;
      __gen_e_acsl_assert_data_7.kind = "RTE";
      __gen_e_acsl_assert_data_7.pred_txt = "f != 0";
      __gen_e_acsl_assert_data_7.file = "rte.i";
      __gen_e_acsl_assert_data_7.fct = "test";
      __gen_e_acsl_assert_data_7.line = 13;
      __gen_e_acsl_assert_data_7.name = "division_by_zero";
      __e_acsl_assert(f != 0,& __gen_e_acsl_assert_data_7);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data_7);
      if (1 % f == 1) __gen_e_acsl_or = 1;
      else {
        __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_6,"g",0,g);
        __e_acsl_assert_data_t __gen_e_acsl_assert_data_8 =
          {.values = (void *)0};
        __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_8,"g",0,g);
        __gen_e_acsl_assert_data_8.blocking = 1;
        __gen_e_acsl_assert_data_8.kind = "RTE";
        __gen_e_acsl_assert_data_8.pred_txt = "g != 0";
        __gen_e_acsl_assert_data_8.file = "rte.i";
        __gen_e_acsl_assert_data_8.fct = "test";
        __gen_e_acsl_assert_data_8.line = 13;
        __gen_e_acsl_assert_data_8.name = "division_by_zero";
        __e_acsl_assert(g != 0,& __gen_e_acsl_assert_data_8);
        __e_acsl_assert_clean(& __gen_e_acsl_assert_data_8);
        __gen_e_acsl_or = 1 % g == 1;
      }
      __e_acsl_assert_data_t __gen_e_acsl_assert_data_9 =
        {.values = (void *)0};
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_9,"h",0,h);
      __e_acsl_assert_data_t __gen_e_acsl_assert_data_10 =
        {.values = (void *)0};
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_10,"h",0,h);
      __gen_e_acsl_assert_data_10.blocking = 1;
      __gen_e_acsl_assert_data_10.kind = "RTE";
      __gen_e_acsl_assert_data_10.pred_txt = "h != 0";
      __gen_e_acsl_assert_data_10.file = "rte.i";
      __gen_e_acsl_assert_data_10.fct = "test";
      __gen_e_acsl_assert_data_10.line = 14;
      __gen_e_acsl_assert_data_10.name = "division_by_zero";
      __e_acsl_assert(h != 0,& __gen_e_acsl_assert_data_10);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data_10);
      if (1 % h == 1) {
        __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_9,"i",0,i);
        __e_acsl_assert_data_t __gen_e_acsl_assert_data_11 =
          {.values = (void *)0};
        __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_11,"i",0,i);
        __gen_e_acsl_assert_data_11.blocking = 1;
        __gen_e_acsl_assert_data_11.kind = "RTE";
        __gen_e_acsl_assert_data_11.pred_txt = "i != 0";
        __gen_e_acsl_assert_data_11.file = "rte.i";
        __gen_e_acsl_assert_data_11.fct = "test";
        __gen_e_acsl_assert_data_11.line = 14;
        __gen_e_acsl_assert_data_11.name = "division_by_zero";
        __e_acsl_assert(i != 0,& __gen_e_acsl_assert_data_11);
        __e_acsl_assert_clean(& __gen_e_acsl_assert_data_11);
        __gen_e_acsl_and = 1 % i == 1;
      }
      else __gen_e_acsl_and = 0;
      __e_acsl_assert_data_t __gen_e_acsl_assert_data_12 =
        {.values = (void *)0};
      __gen_e_acsl_var = 1;
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_12,"var",0,
                                   __gen_e_acsl_var);
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_12,"j",0,j);
      __e_acsl_assert_data_t __gen_e_acsl_assert_data_13 =
        {.values = (void *)0};
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_13,"j",0,j);
      __gen_e_acsl_assert_data_13.blocking = 1;
      __gen_e_acsl_assert_data_13.kind = "RTE";
      __gen_e_acsl_assert_data_13.pred_txt = "j != 0";
      __gen_e_acsl_assert_data_13.file = "rte.i";
      __gen_e_acsl_assert_data_13.fct = "test";
      __gen_e_acsl_assert_data_13.line = 15;
      __gen_e_acsl_assert_data_13.name = "division_by_zero";
      __e_acsl_assert(j != 0,& __gen_e_acsl_assert_data_13);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data_13);
      __e_acsl_assert_data_t __gen_e_acsl_assert_data_14 =
        {.values = (void *)0};
      __gen_e_acsl_forall = 1;
      __gen_e_acsl_var_2 = 0;
      while (1) {
        if (__gen_e_acsl_var_2 < k) ; else break;
        {
          __e_acsl_assert_data_t __gen_e_acsl_assert_data_15 =
            {.values = (void *)0};
          __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_15,"k",0,k);
          __gen_e_acsl_assert_data_15.blocking = 1;
          __gen_e_acsl_assert_data_15.kind = "RTE";
          __gen_e_acsl_assert_data_15.pred_txt = "k != 0";
          __gen_e_acsl_assert_data_15.file = "rte.i";
          __gen_e_acsl_assert_data_15.fct = "test";
          __gen_e_acsl_assert_data_15.line = 16;
          __gen_e_acsl_assert_data_15.name = "division_by_zero";
          __e_acsl_assert(k != 0,& __gen_e_acsl_assert_data_15);
          __e_acsl_assert_clean(& __gen_e_acsl_assert_data_15);
          if (__gen_e_acsl_var_2 % k == __gen_e_acsl_var_2) ;
          else {
            __gen_e_acsl_forall = 0;
            goto e_acsl_end_loop1;
          }
        }
        __gen_e_acsl_var_2 ++;
      }
      e_acsl_end_loop1: ;
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_14,
                                   "bhvr: \\forall integer var; 0 <= var < k ==> var % k == var",
                                   0,__gen_e_acsl_forall);
      __e_acsl_assert_data_t __gen_e_acsl_assert_data_16 =
        {.values = (void *)0};
      __gen_e_acsl_exists = 0;
      __gen_e_acsl_var_3 = 0;
      while (1) {
        if (__gen_e_acsl_var_3 < l) ; else break;
        {
          __e_acsl_assert_data_t __gen_e_acsl_assert_data_17 =
            {.values = (void *)0};
          __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_17,"l",0,l);
          __gen_e_acsl_assert_data_17.blocking = 1;
          __gen_e_acsl_assert_data_17.kind = "RTE";
          __gen_e_acsl_assert_data_17.pred_txt = "l != 0";
          __gen_e_acsl_assert_data_17.file = "rte.i";
          __gen_e_acsl_assert_data_17.fct = "test";
          __gen_e_acsl_assert_data_17.line = 17;
          __gen_e_acsl_assert_data_17.name = "division_by_zero";
          __e_acsl_assert(l != 0,& __gen_e_acsl_assert_data_17);
          __e_acsl_assert_clean(& __gen_e_acsl_assert_data_17);
          if (! (__gen_e_acsl_var_3 % l == __gen_e_acsl_var_3)) ;
          else {
            __gen_e_acsl_exists = 1;
            goto e_acsl_end_loop2;
          }
        }
        __gen_e_acsl_var_3 ++;
      }
      e_acsl_end_loop2: ;
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_16,
                                   "bhvr: \\exists integer var; 0 <= var < l && var % l == var",
                                   0,__gen_e_acsl_exists);
      __gen_e_acsl_assert_data_16.blocking = 1;
      __gen_e_acsl_assert_data_16.kind = "Precondition";
      __gen_e_acsl_assert_data_16.pred_txt = "\\exists integer var; 0 <= var < l && var % l == var";
      __gen_e_acsl_assert_data_16.file = "rte.i";
      __gen_e_acsl_assert_data_16.fct = "test";
      __gen_e_acsl_assert_data_16.line = 17;
      __gen_e_acsl_assert_data_16.name = "bhvr";
      __e_acsl_assert(__gen_e_acsl_exists,& __gen_e_acsl_assert_data_16);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data_16);
      __gen_e_acsl_assert_data_14.blocking = 1;
      __gen_e_acsl_assert_data_14.kind = "Precondition";
      __gen_e_acsl_assert_data_14.pred_txt = "\\forall integer var; 0 <= var < k ==> var % k == var";
      __gen_e_acsl_assert_data_14.file = "rte.i";
      __gen_e_acsl_assert_data_14.fct = "test";
      __gen_e_acsl_assert_data_14.line = 16;
      __gen_e_acsl_assert_data_14.name = "bhvr";
      __e_acsl_assert(__gen_e_acsl_forall,& __gen_e_acsl_assert_data_14);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data_14);
      __gen_e_acsl_assert_data_12.blocking = 1;
      __gen_e_acsl_assert_data_12.kind = "Precondition";
      __gen_e_acsl_assert_data_12.pred_txt = "\\let var = 1; var % j == 1";
      __gen_e_acsl_assert_data_12.file = "rte.i";
      __gen_e_acsl_assert_data_12.fct = "test";
      __gen_e_acsl_assert_data_12.line = 15;
      __gen_e_acsl_assert_data_12.name = "bhvr";
      __e_acsl_assert(__gen_e_acsl_var % j == 1,
                      & __gen_e_acsl_assert_data_12);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data_12);
      __gen_e_acsl_assert_data_9.blocking = 1;
      __gen_e_acsl_assert_data_9.kind = "Precondition";
      __gen_e_acsl_assert_data_9.pred_txt = "1 % h == 1 && 1 % i == 1";
      __gen_e_acsl_assert_data_9.file = "rte.i";
      __gen_e_acsl_assert_data_9.fct = "test";
      __gen_e_acsl_assert_data_9.line = 14;
      __gen_e_acsl_assert_data_9.name = "bhvr";
      __e_acsl_assert(__gen_e_acsl_and,& __gen_e_acsl_assert_data_9);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data_9);
      __gen_e_acsl_assert_data_6.blocking = 1;
      __gen_e_acsl_assert_data_6.kind = "Precondition";
      __gen_e_acsl_assert_data_6.pred_txt = "1 % f == 1 || 1 % g == 1";
      __gen_e_acsl_assert_data_6.file = "rte.i";
      __gen_e_acsl_assert_data_6.fct = "test";
      __gen_e_acsl_assert_data_6.line = 13;
      __gen_e_acsl_assert_data_6.name = "bhvr";
      __e_acsl_assert(__gen_e_acsl_or,& __gen_e_acsl_assert_data_6);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data_6);
      __gen_e_acsl_assert_data_4.blocking = 1;
      __gen_e_acsl_assert_data_4.kind = "Precondition";
      __gen_e_acsl_assert_data_4.pred_txt = "1 % d == 1";
      __gen_e_acsl_assert_data_4.file = "rte.i";
      __gen_e_acsl_assert_data_4.fct = "test";
      __gen_e_acsl_assert_data_4.line = 12;
      __gen_e_acsl_assert_data_4.name = "bhvr";
      __e_acsl_assert(1 % d == 1,& __gen_e_acsl_assert_data_4);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data_4);
    }
  }
  test(a,b,c,d,e,f,g,h,i,j,k,l);
  {
    int __gen_e_acsl_assumes_value_2;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_18 =
      {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_18,"\\old(b)",0,
                                 __gen_e_acsl_at);
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_19 =
      {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_19,
                                 "__gen_e_acsl_at",0,__gen_e_acsl_at);
    __gen_e_acsl_assert_data_19.blocking = 1;
    __gen_e_acsl_assert_data_19.kind = "RTE";
    __gen_e_acsl_assert_data_19.pred_txt = "__gen_e_acsl_at != 0";
    __gen_e_acsl_assert_data_19.file = "rte.i";
    __gen_e_acsl_assert_data_19.fct = "test";
    __gen_e_acsl_assert_data_19.line = 8;
    __gen_e_acsl_assert_data_19.name = "division_by_zero";
    __e_acsl_assert(__gen_e_acsl_at != 0,& __gen_e_acsl_assert_data_19);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_19);
    __gen_e_acsl_assert_data_18.blocking = 1;
    __gen_e_acsl_assert_data_18.kind = "Postcondition";
    __gen_e_acsl_assert_data_18.pred_txt = "1 % \\old(b) == 1";
    __gen_e_acsl_assert_data_18.file = "rte.i";
    __gen_e_acsl_assert_data_18.fct = "test";
    __gen_e_acsl_assert_data_18.line = 8;
    __e_acsl_assert(1 % __gen_e_acsl_at == 1,& __gen_e_acsl_assert_data_18);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_18);
    __gen_e_acsl_assumes_value_2 = __e_acsl_contract_get_behavior_assumes
    ((__e_acsl_contract_t const *)__gen_e_acsl_contract,0UL);
    if (__gen_e_acsl_assumes_value_2) {
      __e_acsl_assert_data_t __gen_e_acsl_assert_data_20 =
        {.values = (void *)0};
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_20,"\\old(e)",
                                   0,__gen_e_acsl_at_2);
      __e_acsl_assert_data_t __gen_e_acsl_assert_data_21 =
        {.values = (void *)0};
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_21,
                                   "__gen_e_acsl_at_2",0,__gen_e_acsl_at_2);
      __gen_e_acsl_assert_data_21.blocking = 1;
      __gen_e_acsl_assert_data_21.kind = "RTE";
      __gen_e_acsl_assert_data_21.pred_txt = "__gen_e_acsl_at_2 != 0";
      __gen_e_acsl_assert_data_21.file = "rte.i";
      __gen_e_acsl_assert_data_21.fct = "test";
      __gen_e_acsl_assert_data_21.line = 18;
      __gen_e_acsl_assert_data_21.name = "division_by_zero";
      __e_acsl_assert(__gen_e_acsl_at_2 != 0,& __gen_e_acsl_assert_data_21);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data_21);
      __gen_e_acsl_assert_data_20.blocking = 1;
      __gen_e_acsl_assert_data_20.kind = "Postcondition";
      __gen_e_acsl_assert_data_20.pred_txt = "1 % \\old(e) == 1";
      __gen_e_acsl_assert_data_20.file = "rte.i";
      __gen_e_acsl_assert_data_20.fct = "test";
      __gen_e_acsl_assert_data_20.line = 18;
      __gen_e_acsl_assert_data_20.name = "bhvr";
      __e_acsl_assert(1 % __gen_e_acsl_at_2 == 1,
                      & __gen_e_acsl_assert_data_20);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data_20);
    }
    __e_acsl_contract_clean(__gen_e_acsl_contract);
    return;
  }
}


