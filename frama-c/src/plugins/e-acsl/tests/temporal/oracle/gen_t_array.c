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
  int *src[3];
  __e_acsl_memory_init((int *)0,(char ***)0,8UL);
  __e_acsl_store_block((void *)(src),24UL);
  int a = 111;
  __e_acsl_store_block((void *)(& a),4UL);
  __e_acsl_full_init((void *)(& a));
  int b = 222;
  __e_acsl_store_block((void *)(& b),4UL);
  __e_acsl_full_init((void *)(& b));
  __e_acsl_initialize((void *)(src),sizeof(int *));
  __e_acsl_temporal_store_nblock((void *)(src),(void *)(& a));
  src[0] = & a;
  __e_acsl_initialize((void *)(& src[1]),sizeof(int *));
  __e_acsl_temporal_store_nblock((void *)(& src[1]),(void *)(& b));
  src[1] = & b;
  {
    int __gen_e_acsl_initialized;
    int __gen_e_acsl_and;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data = {.values = (void *)0};
    __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data,"(int **)src",
                                 (void *)(src));
    __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data,
                                   "sizeof(int *)",0,sizeof(int *));
    __gen_e_acsl_initialized = __e_acsl_initialized((void *)(src),
                                                    sizeof(int *));
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,
                                 "\\initialized((int **)src)",0,
                                 __gen_e_acsl_initialized);
    if (__gen_e_acsl_initialized) {
      int __gen_e_acsl_valid;
      __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data,"src[0]",
                                   (void *)src[0]);
      __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data,
                                     "sizeof(int)",0,sizeof(int));
      __gen_e_acsl_valid = __e_acsl_valid((void *)src[0],sizeof(int),
                                          (void *)src[0],(void *)(src));
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data,
                                   "\\valid(src[0])",0,__gen_e_acsl_valid);
      __gen_e_acsl_and = __gen_e_acsl_valid;
    }
    else __gen_e_acsl_and = 0;
    __gen_e_acsl_assert_data.blocking = 1;
    __gen_e_acsl_assert_data.kind = "Assertion";
    __gen_e_acsl_assert_data.pred_txt = "\\valid(src[0])";
    __gen_e_acsl_assert_data.file = "t_array.c";
    __gen_e_acsl_assert_data.fct = "main";
    __gen_e_acsl_assert_data.line = 12;
    __e_acsl_assert(__gen_e_acsl_and,& __gen_e_acsl_assert_data);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data);
  }
  /*@ assert \valid(src[0]); */ ;
  {
    int __gen_e_acsl_initialized_2;
    int __gen_e_acsl_and_2;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_2 =
      {.values = (void *)0};
    __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data_2,"&src[1]",
                                 (void *)(& src[1]));
    __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data_2,
                                   "sizeof(int *)",0,sizeof(int *));
    __gen_e_acsl_initialized_2 = __e_acsl_initialized((void *)(& src[1]),
                                                      sizeof(int *));
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_2,
                                 "\\initialized(&src[1])",0,
                                 __gen_e_acsl_initialized_2);
    if (__gen_e_acsl_initialized_2) {
      int __gen_e_acsl_valid_2;
      __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data_2,"src[1]",
                                   (void *)src[1]);
      __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data_2,
                                     "sizeof(int)",0,sizeof(int));
      __gen_e_acsl_valid_2 = __e_acsl_valid((void *)src[1],sizeof(int),
                                            (void *)src[1],
                                            (void *)(& src[1]));
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_2,
                                   "\\valid(src[1])",0,__gen_e_acsl_valid_2);
      __gen_e_acsl_and_2 = __gen_e_acsl_valid_2;
    }
    else __gen_e_acsl_and_2 = 0;
    __gen_e_acsl_assert_data_2.blocking = 1;
    __gen_e_acsl_assert_data_2.kind = "Assertion";
    __gen_e_acsl_assert_data_2.pred_txt = "\\valid(src[1])";
    __gen_e_acsl_assert_data_2.file = "t_array.c";
    __gen_e_acsl_assert_data_2.fct = "main";
    __gen_e_acsl_assert_data_2.line = 13;
    __e_acsl_assert(__gen_e_acsl_and_2,& __gen_e_acsl_assert_data_2);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_2);
  }
  /*@ assert \valid(src[1]); */ ;
  {
    int __gen_e_acsl_initialized_3;
    int __gen_e_acsl_and_3;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data_3 =
      {.values = (void *)0};
    __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data_3,"&src[2]",
                                 (void *)(& src[2]));
    __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data_3,
                                   "sizeof(int *)",0,sizeof(int *));
    __gen_e_acsl_initialized_3 = __e_acsl_initialized((void *)(& src[2]),
                                                      sizeof(int *));
    __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_3,
                                 "\\initialized(&src[2])",0,
                                 __gen_e_acsl_initialized_3);
    if (__gen_e_acsl_initialized_3) {
      int __gen_e_acsl_valid_3;
      __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data_3,"src[2]",
                                   (void *)src[2]);
      __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data_3,
                                     "sizeof(int)",0,sizeof(int));
      __gen_e_acsl_valid_3 = __e_acsl_valid((void *)src[2],sizeof(int),
                                            (void *)src[2],
                                            (void *)(& src[2]));
      __e_acsl_assert_register_int(& __gen_e_acsl_assert_data_3,
                                   "\\valid(src[2])",0,__gen_e_acsl_valid_3);
      __gen_e_acsl_and_3 = __gen_e_acsl_valid_3;
    }
    else __gen_e_acsl_and_3 = 0;
    __gen_e_acsl_assert_data_3.blocking = 1;
    __gen_e_acsl_assert_data_3.kind = "Assertion";
    __gen_e_acsl_assert_data_3.pred_txt = "!\\valid(src[2])";
    __gen_e_acsl_assert_data_3.file = "t_array.c";
    __gen_e_acsl_assert_data_3.fct = "main";
    __gen_e_acsl_assert_data_3.line = 14;
    __e_acsl_assert(! __gen_e_acsl_and_3,& __gen_e_acsl_assert_data_3);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data_3);
  }
  /*@ assert !\valid(src[2]); */ ;
  __retres = 0;
  __e_acsl_delete_block((void *)(src));
  __e_acsl_delete_block((void *)(& b));
  __e_acsl_delete_block((void *)(& a));
  __e_acsl_memory_clean();
  return __retres;
}

