/* Generated by Frama-C */
#include "pthread.h"
#include "sched.h"
#include "signal.h"
#include "stddef.h"
#include "stdint.h"
#include "stdio.h"
#include "time.h"
extern  __attribute__((__FC_BUILTIN__)) int __e_acsl_sound_verdict;

int a = 0;
int b;
void __e_acsl_globals_init(void)
{
  static char __e_acsl_already_run = 0;
  if (! __e_acsl_already_run) {
    __e_acsl_already_run = 1;
    __e_acsl_store_block((void *)(& b),4UL);
    __e_acsl_full_init((void *)(& b));
    __e_acsl_store_block((void *)(& a),4UL);
    __e_acsl_full_init((void *)(& a));
  }
  return;
}

void __e_acsl_globals_clean(void)
{
  __e_acsl_delete_block((void *)(& b));
  __e_acsl_delete_block((void *)(& a));
  return;
}

int main(void)
{
  int __retres;
  __e_acsl_memory_init((int *)0,(char ***)0,8UL);
  __e_acsl_globals_init();
  int *p = & a;
  __e_acsl_store_block((void *)(& p),8UL);
  __e_acsl_full_init((void *)(& p));
  int *q = & b;
  __e_acsl_store_block((void *)(& q),8UL);
  __e_acsl_full_init((void *)(& q));
  {
    __e_acsl_assert_data_t __gen_e_acsl_assert_data = {.values = (void *)0};
    __gen_e_acsl_assert_data.blocking = 1;
    __gen_e_acsl_assert_data.kind = "Assertion";
    __gen_e_acsl_assert_data.pred_txt = "\\initialized(&b)";
    __gen_e_acsl_assert_data.file = "init.c";
    __gen_e_acsl_assert_data.fct = "main";
    __gen_e_acsl_assert_data.line = 9;
    __e_acsl_assert(1,& __gen_e_acsl_assert_data);
  }
  /*@ assert \initialized(&b); */ ;
  {
    int __gen_e_acsl_initialized;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_2 =
      {.values = (void *)0};
    __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data_2,"q",(void *)q);
    __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data_2,
                                   "sizeof(int)",0,sizeof(int));
    __gen_e_acsl_initialized = __e_acsl_initialized((void *)q,sizeof(int));
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_2,
                                 "\\initialized(q)",0,
                                 __gen_e_acsl_initialized);
    __gen_e_acsl_assert_data_2.blocking = 1;
    __gen_e_acsl_assert_data_2.kind = "Assertion";
    __gen_e_acsl_assert_data_2.pred_txt = "\\initialized(q)";
    __gen_e_acsl_assert_data_2.file = "init.c";
    __gen_e_acsl_assert_data_2.fct = "main";
    __gen_e_acsl_assert_data_2.line = 10;
    __e_acsl_assert(__gen_e_acsl_initialized,& __gen_e_acsl_assert_data_2);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_2);
  }
  /*@ assert \initialized(q); */ ;
  {
    int __gen_e_acsl_initialized_2;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_3 =
      {.values = (void *)0};
    __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data_3,"p",(void *)p);
    __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data_3,
                                   "sizeof(int)",0,sizeof(int));
    __gen_e_acsl_initialized_2 = __e_acsl_initialized((void *)p,sizeof(int));
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_3,
                                 "\\initialized(p)",0,
                                 __gen_e_acsl_initialized_2);
    __gen_e_acsl_assert_data_3.blocking = 1;
    __gen_e_acsl_assert_data_3.kind = "Assertion";
    __gen_e_acsl_assert_data_3.pred_txt = "\\initialized(p)";
    __gen_e_acsl_assert_data_3.file = "init.c";
    __gen_e_acsl_assert_data_3.fct = "main";
    __gen_e_acsl_assert_data_3.line = 11;
    __e_acsl_assert(__gen_e_acsl_initialized_2,& __gen_e_acsl_assert_data_3);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_3);
  }
  /*@ assert \initialized(p); */ ;
  __retres = 0;
  __e_acsl_delete_block((void *)(& q));
  __e_acsl_delete_block((void *)(& p));
  __e_acsl_globals_clean();
  __e_acsl_memory_clean();
  return __retres;
}

