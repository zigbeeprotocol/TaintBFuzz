/* Generated by Frama-C */
#include "pthread.h"
#include "sched.h"
#include "signal.h"
#include "stddef.h"
#include "stdint.h"
#include "stdio.h"
#include "time.h"
char *__gen_e_acsl_literal_string_2;
char *__gen_e_acsl_literal_string_3;
char *__gen_e_acsl_literal_string;
char *__gen_e_acsl_literal_string_4;
extern  __attribute__((__FC_BUILTIN__)) int __e_acsl_sound_verdict;

void __e_acsl_globals_init(void)
{
  static char __e_acsl_already_run = 0;
  if (! __e_acsl_already_run) {
    __e_acsl_already_run = 1;
    __gen_e_acsl_literal_string_2 = "t is %d, going to %s\n";
    __e_acsl_store_block((void *)__gen_e_acsl_literal_string_2,
                         sizeof("t is %d, going to %s\n"));
    __e_acsl_full_init((void *)__gen_e_acsl_literal_string_2);
    __e_acsl_mark_readonly((void *)__gen_e_acsl_literal_string_2);
    __gen_e_acsl_literal_string_3 = "UP";
    __e_acsl_store_block((void *)__gen_e_acsl_literal_string_3,sizeof("UP"));
    __e_acsl_full_init((void *)__gen_e_acsl_literal_string_3);
    __e_acsl_mark_readonly((void *)__gen_e_acsl_literal_string_3);
    __gen_e_acsl_literal_string = "RET";
    __e_acsl_store_block((void *)__gen_e_acsl_literal_string,sizeof("RET"));
    __e_acsl_full_init((void *)__gen_e_acsl_literal_string);
    __e_acsl_mark_readonly((void *)__gen_e_acsl_literal_string);
    __gen_e_acsl_literal_string_4 = "AGAIN";
    __e_acsl_store_block((void *)__gen_e_acsl_literal_string_4,
                         sizeof("AGAIN"));
    __e_acsl_full_init((void *)__gen_e_acsl_literal_string_4);
    __e_acsl_mark_readonly((void *)__gen_e_acsl_literal_string_4);
  }
  return;
}

int main(int argc, char const **argv)
{
  int __retres;
  __e_acsl_memory_init(& argc,(char ***)(& argv),8UL);
  __e_acsl_globals_init();
  int t = 0;
  UP: ;
  if (t == 2) {
    printf(__gen_e_acsl_literal_string_2,t,
           (char *)__gen_e_acsl_literal_string); /* printf_va_1 */
    goto RET;
  }
  AGAIN:
  {
    int a;
    __e_acsl_store_block((void *)(& a),4UL);
    __e_acsl_full_init((void *)(& a));
    a = 1;
    {
      int __gen_e_acsl_valid;
      __e_acsl_assert_data_t __gen_e_acsl_assert_data =
        {.values = (void *)0};
      __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data,"&a",
                                   (void *)(& a));
      __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data,
                                     "sizeof(int)",0,sizeof(int));
      __gen_e_acsl_valid = __e_acsl_valid((void *)(& a),sizeof(int),
                                          (void *)(& a),(void *)0);
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,"\\valid(&a)",
                                   0,__gen_e_acsl_valid);
      __gen_e_acsl_assert_data.blocking = 1;
      __gen_e_acsl_assert_data.kind = "Assertion";
      __gen_e_acsl_assert_data.pred_txt = "\\valid(&a)";
      __gen_e_acsl_assert_data.file = "local_goto.c";
      __gen_e_acsl_assert_data.fct = "main";
      __gen_e_acsl_assert_data.line = 23;
      __e_acsl_assert(__gen_e_acsl_valid,& __gen_e_acsl_assert_data);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data);
    }
    /*@ assert \valid(&a); */ ;
    if (t == 2) {
      printf(__gen_e_acsl_literal_string_2,t,
             (char *)__gen_e_acsl_literal_string_3); /* printf_va_2 */
      __e_acsl_delete_block((void *)(& a));
      goto UP;
    }
    else t ++;
    int b = 15;
    __e_acsl_store_block((void *)(& b),4UL);
    __e_acsl_full_init((void *)(& b));
    {
      int __gen_e_acsl_valid_2;
      __e_acsl_assert_data_t __gen_e_acsl_assert_data_2 =
        {.values = (void *)0};
      __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data_2,"&b",
                                   (void *)(& b));
      __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data_2,
                                     "sizeof(int)",0,sizeof(int));
      __gen_e_acsl_valid_2 = __e_acsl_valid((void *)(& b),sizeof(int),
                                            (void *)(& b),(void *)0);
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_2,
                                   "\\valid(&b)",0,__gen_e_acsl_valid_2);
      __gen_e_acsl_assert_data_2.blocking = 1;
      __gen_e_acsl_assert_data_2.kind = "Assertion";
      __gen_e_acsl_assert_data_2.pred_txt = "\\valid(&b)";
      __gen_e_acsl_assert_data_2.file = "local_goto.c";
      __gen_e_acsl_assert_data_2.fct = "main";
      __gen_e_acsl_assert_data_2.line = 34;
      __e_acsl_assert(__gen_e_acsl_valid_2,& __gen_e_acsl_assert_data_2);
      __e_acsl_assert_clean(& __gen_e_acsl_assert_data_2);
    }
    /*@ assert \valid(&b); */ ;
    printf(__gen_e_acsl_literal_string_2,t,
           (char *)__gen_e_acsl_literal_string_4); /* printf_va_3 */
    __e_acsl_delete_block((void *)(& a));
    __e_acsl_delete_block((void *)(& b));
    goto AGAIN;
    __e_acsl_delete_block((void *)(& b));
    __e_acsl_delete_block((void *)(& a));
  }
  RET: __retres = 0;
  __e_acsl_memory_clean();
  return __retres;
}


