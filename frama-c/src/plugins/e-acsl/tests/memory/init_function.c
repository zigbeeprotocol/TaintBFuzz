/* run.config
  COMMENT: Check that the instrumentation engine still adds __e_acsl_memory_init
  COMMENT: if no variable is instrumented.
  STDOPT: +"-eva-no-builtins-auto"
*/

#include <stdlib.h>

extern size_t __e_acsl_heap_allocation_size;

int main(void) {
  // The asserts check that the memory model of E-ACSL is correctly initialized
  // and updated, but since no memory predicate is used the variable `a` does
  // not need to be instrumented (ie. no `store_block` and `delete_block` are
  // generated).
  /*@ assert __e_acsl_heap_allocation_size == 0;  */
  char *a = malloc(7);
  /*@ assert __e_acsl_heap_allocation_size == 7;  */
}
