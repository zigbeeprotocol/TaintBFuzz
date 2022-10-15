/* run.config
 COMMENT: Test `strlen` E-ACSL built-ins
 DEPS: @PTEST_DEPS@ utils/signalled.h
   STDOPT:
 COMMENT: This part is blank on purpose (test stability + Dune)




*/

#include "utils/signalled.h"
#include <stdlib.h>
#include <string.h>

#define EQ(l, r)                                                               \
  if (l != r)                                                                  \
    abort();

int main(int argc, const char **argv) {
  int len;
  char *empty_str = "";
  char *heap_str = strdup("the cat");
  char stack_str[] = "the dog";
  char *const_str = "the hog";

  // strlen on a valid (zero-length) string [ok]:
  OK(EQ(len = strlen(empty_str), 0));
  OK(EQ(len = strlen(heap_str), 7));  // strlen on a heap string [ok]
  OK(EQ(len = strlen(stack_str), 7)); // strlen on a stack string [ok]
  OK(EQ(len = strlen(const_str), 7)); // strlen on a const string [ok]

  heap_str[7] = 'a';
  stack_str[7] = 'a';
  // strlen on unterminated heap string [abort]:
  ABRT(EQ(len = strlen(heap_str), 7));
  // strlen on unterminated stack string [abort]:
  ABRT(EQ(len = strlen(stack_str), 7));
  free(heap_str);
  ABRT(EQ(len = strlen(heap_str), 7)); // strlen on invalid heap string [abort]
  return 0;
}
