/* Generated by Frama-C */
#include "pthread.h"
#include "sched.h"
#include "signal.h"
#include "stddef.h"
#include "stdint.h"
#include "stdio.h"
#include "time.h"
extern  __attribute__((__FC_BUILTIN__)) int __e_acsl_sound_verdict;

/*@ requires \initialized(p);
    requires *p == 0;
    ensures \result == \old(*p); */
int __gen_e_acsl_f(int *p);

int f(int *p)
{
  int __retres;
  __e_acsl_store_block((void *)(& p),8UL);
  {
    int i = 0;
    {
      int __gen_e_acsl_and;
      __e_acsl_assert_data_t __gen_e_acsl_assert_data =
        {.values = (void *)0};
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,"i",0,i);
      if (0 <= i) {
        __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,"i",0,i);
        __gen_e_acsl_and = i <= 1;
      }
      else __gen_e_acsl_and = 0;
      __gen_e_acsl_assert_data.blocking = 1;
      __gen_e_acsl_assert_data.kind = "Invariant";
      __gen_e_acsl_assert_data.pred_txt = "0 <= i <= 1";
      __gen_e_acsl_assert_data.file = "e-acsl-functions.c";
      __gen_e_acsl_assert_data.fct = "f";
      __gen_e_acsl_assert_data.line = 13;
      __e_acsl_assert(__gen_e_acsl_and,& __gen_e_acsl_assert_data);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data);
    }
    /*@ loop invariant 0 <= i <= 1; */
    while (i < 1) {
      int __gen_e_acsl_and_2;
      i ++;
      __e_acsl_assert_data_t __gen_e_acsl_assert_data_2 =
        {.values = (void *)0};
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_2,"i",0,i);
      if (0 <= i) {
        __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_2,"i",0,i);
        __gen_e_acsl_and_2 = i <= 1;
      }
      else __gen_e_acsl_and_2 = 0;
      __gen_e_acsl_assert_data_2.blocking = 1;
      __gen_e_acsl_assert_data_2.kind = "Invariant";
      __gen_e_acsl_assert_data_2.pred_txt = "0 <= i <= 1";
      __gen_e_acsl_assert_data_2.file = "e-acsl-functions.c";
      __gen_e_acsl_assert_data_2.fct = "f";
      __gen_e_acsl_assert_data_2.line = 13;
      __e_acsl_assert(__gen_e_acsl_and_2,& __gen_e_acsl_assert_data_2);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data_2);
    }
  }
  __retres = 0;
  __e_acsl_delete_block((void *)(& p));
  return __retres;
}

/*@ requires \initialized(p);
    requires *p == 1;
    ensures \result == \old(*p); */
int g(int *p)
{
  int __retres;
  {
    int i = 0;
    /*@ loop invariant 0 <= i <= 1; */
    while (i < 1) i ++;
  }
  __retres = 0;
  return __retres;
}

int main(void)
{
  int __retres;
  __e_acsl_memory_init((int *)0,(char ***)0,8UL);
  int x = 0;
  __e_acsl_store_block((void *)(& x),4UL);
  __e_acsl_full_init((void *)(& x));
  int y = 0;
  __gen_e_acsl_f(& x);
  g(& y);
  __retres = 0;
  __e_acsl_delete_block((void *)(& x));
  __e_acsl_memory_clean();
  return __retres;
}

/*@ requires \initialized(p);
    requires *p == 0;
    ensures \result == \old(*p); */
int __gen_e_acsl_f(int *p)
{
  int __gen_e_acsl_at;
  int __retres;
  {
    int __gen_e_acsl_valid_read;
    int __gen_e_acsl_initialized;
    int __gen_e_acsl_valid_read_2;
    __e_acsl_store_block((void *)(& p),8UL);
    __e_acsl_assert_data_t __gen_e_acsl_assert_data = {.values = (void *)0};
    __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data,"p",(void *)p);
    __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data,"sizeof(int)",
                                   0,sizeof(int));
    __gen_e_acsl_valid_read = __e_acsl_valid_read((void *)p,sizeof(int),
                                                  (void *)p,(void *)(& p));
    __gen_e_acsl_assert_data.blocking = 1;
    __gen_e_acsl_assert_data.kind = "RTE";
    __gen_e_acsl_assert_data.pred_txt = "\\valid_read(p)";
    __gen_e_acsl_assert_data.file = "e-acsl-functions.c";
    __gen_e_acsl_assert_data.fct = "f";
    __gen_e_acsl_assert_data.line = 11;
    __gen_e_acsl_assert_data.name = "mem_access";
    __e_acsl_assert(__gen_e_acsl_valid_read,& __gen_e_acsl_assert_data);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data);
    __gen_e_acsl_at = *p;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_2 =
      {.values = (void *)0};
    __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data_2,"p",(void *)p);
    __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data_2,
                                   "sizeof(int)",0,sizeof(int));
    __gen_e_acsl_initialized = __e_acsl_initialized((void *)p,sizeof(int));
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_2,
                                 "\\initialized(p)",0,
                                 __gen_e_acsl_initialized);
    __gen_e_acsl_assert_data_2.blocking = 1;
    __gen_e_acsl_assert_data_2.kind = "Precondition";
    __gen_e_acsl_assert_data_2.pred_txt = "\\initialized(p)";
    __gen_e_acsl_assert_data_2.file = "e-acsl-functions.c";
    __gen_e_acsl_assert_data_2.fct = "f";
    __gen_e_acsl_assert_data_2.line = 9;
    __e_acsl_assert(__gen_e_acsl_initialized,& __gen_e_acsl_assert_data_2);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_2);
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_3 =
      {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_3,"*p",0,*p);
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_4 =
      {.values = (void *)0};
    __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data_4,"p",(void *)p);
    __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data_4,
                                   "sizeof(int)",0,sizeof(int));
    __gen_e_acsl_valid_read_2 = __e_acsl_valid_read((void *)p,sizeof(int),
                                                    (void *)p,(void *)(& p));
    __gen_e_acsl_assert_data_4.blocking = 1;
    __gen_e_acsl_assert_data_4.kind = "RTE";
    __gen_e_acsl_assert_data_4.pred_txt = "\\valid_read(p)";
    __gen_e_acsl_assert_data_4.file = "e-acsl-functions.c";
    __gen_e_acsl_assert_data_4.fct = "f";
    __gen_e_acsl_assert_data_4.line = 10;
    __gen_e_acsl_assert_data_4.name = "mem_access";
    __e_acsl_assert(__gen_e_acsl_valid_read_2,& __gen_e_acsl_assert_data_4);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_4);
    __gen_e_acsl_assert_data_3.blocking = 1;
    __gen_e_acsl_assert_data_3.kind = "Precondition";
    __gen_e_acsl_assert_data_3.pred_txt = "*p == 0";
    __gen_e_acsl_assert_data_3.file = "e-acsl-functions.c";
    __gen_e_acsl_assert_data_3.fct = "f";
    __gen_e_acsl_assert_data_3.line = 10;
    __e_acsl_assert(*p == 0,& __gen_e_acsl_assert_data_3);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_3);
  }
  __retres = f(p);
  {
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_5 =
      {.values = (void *)0};
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_5,"\\result",0,
                                 __retres);
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_5,"\\old(*p)",0,
                                 __gen_e_acsl_at);
    __gen_e_acsl_assert_data_5.blocking = 1;
    __gen_e_acsl_assert_data_5.kind = "Postcondition";
    __gen_e_acsl_assert_data_5.pred_txt = "\\result == \\old(*p)";
    __gen_e_acsl_assert_data_5.file = "e-acsl-functions.c";
    __gen_e_acsl_assert_data_5.fct = "f";
    __gen_e_acsl_assert_data_5.line = 11;
    __e_acsl_assert(__retres == __gen_e_acsl_at,& __gen_e_acsl_assert_data_5);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_5);
    __e_acsl_delete_block((void *)(& p));
    return __retres;
  }
}


