/* Generated by Frama-C */
#include "pthread.h"
#include "sched.h"
#include "signal.h"
#include "stddef.h"
#include "stdint.h"
#include "stdio.h"
#include "stdlib.h"
#include "time.h"
extern  __attribute__((__FC_BUILTIN__)) int __e_acsl_sound_verdict;

struct list {
   struct list *next ;
   int value ;
};
/*@
logic integer length_aux{L}(struct list *l, integer n) =
  \at(n < 0? -1:
        (l == (struct list *)0? n:
           (n < 2147483647? length_aux(l->next, n + 1): -1)),
      L);
 */
/*@ logic integer length{L}(struct list *l) = \at(length_aux(l, 0),L);

*/
int main(void)
{
  int __retres;
  struct list node1;
  struct list node2;
  struct list node3;
  __e_acsl_memory_init((int *)0,(char ***)0,8UL);
  __e_acsl_store_block((void *)(& node3),16UL);
  __e_acsl_store_block((void *)(& node2),16UL);
  __e_acsl_store_block((void *)(& node1),16UL);
  __e_acsl_initialize((void *)(& node1.next),sizeof(struct list *));
  node1.next = & node2;
  __e_acsl_initialize((void *)(& node2.next),sizeof(struct list *));
  node2.next = & node3;
  struct list *l = & node1;
  __e_acsl_store_block((void *)(& l),8UL);
  __e_acsl_full_init((void *)(& l));
  /*@ assert length(l) == 3; */ ;
  __retres = 0;
  __e_acsl_delete_block((void *)(& l));
  __e_acsl_delete_block((void *)(& node3));
  __e_acsl_delete_block((void *)(& node2));
  __e_acsl_delete_block((void *)(& node1));
  __e_acsl_memory_clean();
  return __retres;
}


