/* Generated by Frama-C */
#include "errno.h"
#include "pthread.h"
#include "sched.h"
#include "signal.h"
#include "stddef.h"
#include "stdint.h"
#include "stdio.h"
#include "stdlib.h"
#include "time.h"
extern  __attribute__((__FC_BUILTIN__)) int __e_acsl_sound_verdict;

void __e_acsl_globals_init(void)
{
  static char __e_acsl_already_run = 0;
  if (! __e_acsl_already_run) {
    __e_acsl_already_run = 1;
    __e_acsl_store_block((void *)(& errno),4UL);
    __e_acsl_full_init((void *)(& errno));
  }
  return;
}

void __e_acsl_globals_clean(void)
{
  __e_acsl_delete_block((void *)(& errno));
  return;
}

int main(int argc, char const **argv)
{
  int __retres;
  __e_acsl_memory_init(& argc,(char ***)(& argv),8UL);
  __e_acsl_globals_init();
  int *p = & errno;
  __e_acsl_store_block((void *)(& p),8UL);
  __e_acsl_full_init((void *)(& p));
  {
    int __gen_e_acsl_initialized;
    int __gen_e_acsl_and;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data = {.values = (void *)0};
    __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data,"&p",
                                 (void *)(& p));
    __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data,
                                   "sizeof(int *)",0,sizeof(int *));
    __gen_e_acsl_initialized = __e_acsl_initialized((void *)(& p),
                                                    sizeof(int *));
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,
                                 "\\initialized(&p)",0,
                                 __gen_e_acsl_initialized);
    if (__gen_e_acsl_initialized) {
      int __gen_e_acsl_valid;
      __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data,"p",(void *)p);
      __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data,
                                     "sizeof(int)",0,sizeof(int));
      __gen_e_acsl_valid = __e_acsl_valid((void *)p,sizeof(int),(void *)p,
                                          (void *)(& p));
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,"\\valid(p)",0,
                                   __gen_e_acsl_valid);
      __gen_e_acsl_and = __gen_e_acsl_valid;
    }
    else __gen_e_acsl_and = 0;
    __gen_e_acsl_assert_data.blocking = 1;
    __gen_e_acsl_assert_data.kind = "Assertion";
    __gen_e_acsl_assert_data.pred_txt = "\\valid(p)";
    __gen_e_acsl_assert_data.file = "errno.c";
    __gen_e_acsl_assert_data.fct = "main";
    __gen_e_acsl_assert_data.line = 11;
    __e_acsl_assert(__gen_e_acsl_and,& __gen_e_acsl_assert_data);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data);
  }
  /*@ assert \valid(p); */ ;
  __retres = 0;
  __e_acsl_delete_block((void *)(& p));
  __e_acsl_globals_clean();
  __e_acsl_memory_clean();
  return __retres;
}


