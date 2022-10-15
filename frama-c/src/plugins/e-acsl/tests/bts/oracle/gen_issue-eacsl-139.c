/* Generated by Frama-C */
#include "pthread.h"
#include "sched.h"
#include "signal.h"
#include "stddef.h"
#include "stdint.h"
#include "stdio.h"
#include "time.h"
extern  __attribute__((__FC_BUILTIN__)) int __e_acsl_sound_verdict;

struct X {
   int i ;
};
/*@ ensures *\old(item) == \old(*item); */
void __gen_e_acsl_f(struct X *item);

void f(struct X *item)
{
  __e_acsl_store_block((void *)(& item),8UL);
  __e_acsl_delete_block((void *)(& item));
  return;
}

int main(void)
{
  int __retres;
  __e_acsl_memory_init((int *)0,(char ***)0,8UL);
  struct X x = {.i = 1};
  __e_acsl_store_block((void *)(& x),4UL);
  __e_acsl_full_init((void *)(& x));
  __gen_e_acsl_f(& x);
  __retres = 0;
  __e_acsl_delete_block((void *)(& x));
  __e_acsl_memory_clean();
  return __retres;
}

/*@ ensures *\old(item) == \old(*item); */
void __gen_e_acsl_f(struct X *item)
{
  struct X __gen_e_acsl_at_2;
  struct X *__gen_e_acsl_at;
  {
    int __gen_e_acsl_valid_read;
    __e_acsl_store_block((void *)(& item),8UL);
    __gen_e_acsl_at = item;
    __e_acsl_assert_data_t __gen_e_acsl_assert_data = {.values = (void *)0};
    __e_acsl_assert_register_ptr(& __gen_e_acsl_assert_data,"item",
                                 (void *)item);
    __e_acsl_assert_register_ulong(& __gen_e_acsl_assert_data,
                                   "sizeof(struct X)",0,sizeof(struct X));
    __gen_e_acsl_valid_read = __e_acsl_valid_read((void *)item,
                                                  sizeof(struct X),
                                                  (void *)item,
                                                  (void *)(& item));
    __gen_e_acsl_assert_data.blocking = 1;
    __gen_e_acsl_assert_data.kind = "RTE";
    __gen_e_acsl_assert_data.pred_txt = "\\valid_read(item)";
    __gen_e_acsl_assert_data.file = "issue-eacsl-139.c";
    __gen_e_acsl_assert_data.fct = "f";
    __gen_e_acsl_assert_data.line = 9;
    __gen_e_acsl_assert_data.name = "mem_access";
    __e_acsl_assert(__gen_e_acsl_valid_read,& __gen_e_acsl_assert_data);
    __e_acsl_assert_clean(& __gen_e_acsl_assert_data);
    __gen_e_acsl_at_2 = *item;
  }
  f(item);
  __e_acsl_delete_block((void *)(& item));
  return;
}

