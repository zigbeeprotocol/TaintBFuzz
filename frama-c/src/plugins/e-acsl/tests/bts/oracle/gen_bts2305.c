/* Generated by Frama-C */
#include "pthread.h"
#include "sched.h"
#include "signal.h"
#include "stddef.h"
#include "stdint.h"
#include "stdio.h"
#include "time.h"
extern  __attribute__((__FC_BUILTIN__)) int __e_acsl_sound_verdict;

struct bitfields {
   int i : 2 ;
   _Bool j : 1 ;
};
struct bitfields t;
int test(struct bitfields *a)
{
  int __retres;
  __retres = (int)a->i;
  return __retres;
}

void __e_acsl_globals_init(void)
{
  static char __e_acsl_already_run = 0;
  if (! __e_acsl_already_run) {
    __e_acsl_already_run = 1;
    __e_acsl_store_block((void *)(& t),4UL);
    __e_acsl_full_init((void *)(& t));
  }
  return;
}

void __e_acsl_globals_clean(void)
{
  __e_acsl_delete_block((void *)(& t));
  return;
}

int main(int argc, char **argv)
{
  int tmp;
  __e_acsl_memory_init(& argc,& argv,8UL);
  __e_acsl_globals_init();
  /*@ assert \valid_read(&t.j); */ ;
  /*@ assert \valid_read(&t.j + (1 .. 3)); */ ;
  ;
  t.j = (_Bool)1;
  /*@ assert \initialized(&t.j); */ ;
  tmp = test(& t);
  __e_acsl_globals_clean();
  __e_acsl_memory_clean();
  return tmp;
}

