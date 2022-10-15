/* run.config
   STDOPT: #"-eva-no-builtins-auto -eva-slevel 10 -eva-builtin calloc:Frama_C_calloc -eva-alloc-builtin by_stack -eva-msg-key malloc"
   STDOPT: #"-eva-no-builtins-auto -eva-slevel 10 -eva-builtin calloc:Frama_C_calloc -eva-alloc-builtin by_stack -eva-no-alloc-returns-null -eva-msg-key malloc"
   STDOPT: #"-eva-no-builtins-auto"
*/ // slevel is used to unroll loops

#define malloc(n) Frama_C_malloc(n)
#include "stdlib.c"
#include "__fc_builtin.h"
#include <stdint.h>
#include <limits.h>

int main() {
  // always succeeds if -eva-no-alloc-returns-null, otherwise may succeed
  int *p = calloc(1, sizeof(int));
  if (p) {
    //@ assert \valid(p);
  }

  // partial overflow
  size_t nmemb = Frama_C_size_t_interval(1, SIZE_MAX);
  int *q = calloc(nmemb, sizeof(int));
  if (q) {
    //@ assert \valid(q);
  }

  // never succeeds (always overflows)
  int *r = calloc(SIZE_MAX, sizeof(int));
  //@ assert !r;
  int *s;
  // may succeed for some cases, but fail later
  for (size_t i = 1; i < SIZE_MAX; i++) {
    s = calloc(i, sizeof(int));
    if (s) s[i-1] = 42;
  }

  char *p_al0, *p_al1;
  int p_memal_res = posix_memalign((void**)&p_al0, 32, 0);
  free(p_al0);
  int p_memal_res2 = posix_memalign((void**)&p_al1, 32, 42);
  free(p_al1);

  //__fc_realpath test
  char *resolved_name = malloc(PATH_MAX);
  if (!resolved_name) return 1;
  char *realpath_res = realpath("/bin/ls", resolved_name);
  if (realpath_res) {
    //@ assert valid_if_exact: valid_read_string(realpath_res);
  }
  if (Frama_C_nondet(0, 1)) {
    //@ assert maybe_uninitialized: \initialized(resolved_name + PATH_MAX-1);
  }
  free(resolved_name);
  realpath_res = realpath("/bin/ls", NULL);

  char *canon = canonicalize_file_name("/bin/../etc");
  free(canon);

  return 0;
}
