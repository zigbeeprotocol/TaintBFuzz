/* Generated by Frama-C */
#include "pthread.h"
#include "sched.h"
#include "signal.h"
#include "stddef.h"
#include "stdint.h"
#include "stdio.h"
#include "time.h"
extern  __attribute__((__FC_BUILTIN__)) int __e_acsl_sound_verdict;

void __e_acsl_globals_init(void)
{
  static char __e_acsl_already_run = 0;
  if (! __e_acsl_already_run) {
    __e_acsl_already_run = 1;
    __e_acsl_store_block((void *)(& stdout),8UL);
    __e_acsl_full_init((void *)(& stdout));
    __e_acsl_store_block((void *)(& stdin),8UL);
    __e_acsl_full_init((void *)(& stdin));
    __e_acsl_store_block((void *)(& stderr),8UL);
    __e_acsl_full_init((void *)(& stderr));
  }
  return;
}

void __e_acsl_globals_clean(void)
{
  __e_acsl_delete_block((void *)(& stdout));
  __e_acsl_delete_block((void *)(& stdin));
  __e_acsl_delete_block((void *)(& stderr));
  return;
}

int main(void)
{
  int __retres;
  __e_acsl_memory_init((int *)0,(char ***)0,8UL);
  __e_acsl_globals_init();
  {
    int __gen_e_acsl_valid;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data = {.values = (void *)0};
    __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data,"__fc_stderr",
                                 (void *)stderr);
    __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data,"sizeof(FILE)",
                                   0,sizeof(FILE));
    __gen_e_acsl_valid = __e_acsl_valid((void *)stderr,sizeof(FILE),
                                        (void *)stderr,(void *)(& stderr));
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,
                                 "\\valid(__fc_stderr)",0,__gen_e_acsl_valid);
    __gen_e_acsl_assert_data.blocking = 1;
    __gen_e_acsl_assert_data.kind = "Assertion";
    __gen_e_acsl_assert_data.pred_txt = "\\valid(__fc_stderr)";
    __gen_e_acsl_assert_data.file = "stdout.c";
    __gen_e_acsl_assert_data.fct = "main";
    __gen_e_acsl_assert_data.line = 8;
    __e_acsl_assert(__gen_e_acsl_valid,& __gen_e_acsl_assert_data);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data);
  }
  /*@ assert \valid(__fc_stderr); */ ;
  {
    int __gen_e_acsl_valid_2;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_2 =
      {.values = (void *)0};
    __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data_2,"__fc_stdin",
                                 (void *)stdin);
    __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data_2,
                                   "sizeof(FILE)",0,sizeof(FILE));
    __gen_e_acsl_valid_2 = __e_acsl_valid((void *)stdin,sizeof(FILE),
                                          (void *)stdin,(void *)(& stdin));
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_2,
                                 "\\valid(__fc_stdin)",0,
                                 __gen_e_acsl_valid_2);
    __gen_e_acsl_assert_data_2.blocking = 1;
    __gen_e_acsl_assert_data_2.kind = "Assertion";
    __gen_e_acsl_assert_data_2.pred_txt = "\\valid(__fc_stdin)";
    __gen_e_acsl_assert_data_2.file = "stdout.c";
    __gen_e_acsl_assert_data_2.fct = "main";
    __gen_e_acsl_assert_data_2.line = 9;
    __e_acsl_assert(__gen_e_acsl_valid_2,& __gen_e_acsl_assert_data_2);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_2);
  }
  /*@ assert \valid(__fc_stdin); */ ;
  {
    int __gen_e_acsl_valid_3;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_3 =
      {.values = (void *)0};
    __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data_3,"__fc_stdout",
                                 (void *)stdout);
    __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data_3,
                                   "sizeof(FILE)",0,sizeof(FILE));
    __gen_e_acsl_valid_3 = __e_acsl_valid((void *)stdout,sizeof(FILE),
                                          (void *)stdout,(void *)(& stdout));
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_3,
                                 "\\valid(__fc_stdout)",0,
                                 __gen_e_acsl_valid_3);
    __gen_e_acsl_assert_data_3.blocking = 1;
    __gen_e_acsl_assert_data_3.kind = "Assertion";
    __gen_e_acsl_assert_data_3.pred_txt = "\\valid(__fc_stdout)";
    __gen_e_acsl_assert_data_3.file = "stdout.c";
    __gen_e_acsl_assert_data_3.fct = "main";
    __gen_e_acsl_assert_data_3.line = 10;
    __e_acsl_assert(__gen_e_acsl_valid_3,& __gen_e_acsl_assert_data_3);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_3);
  }
  /*@ assert \valid(__fc_stdout); */ ;
  __retres = 0;
  __e_acsl_globals_clean();
  __e_acsl_memory_clean();
  return __retres;
}

