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
  __e_acsl_memory_init((int *)0,(char ***)0,8UL);
  __e_acsl_store_block((void *)(& __retres),4UL);
  __e_acsl_full_init((void *)(& __retres));
  __retres = 0;
  __e_acsl_delete_block((void *)(& __retres));
  __e_acsl_memory_clean();
  return __retres;
}


