/* run.config
PLUGIN: variadic
   LOG: @PTEST_NAME@.pretty.c
   OPT: %{dep:@PTEST_DIR@/empty.c} -no-print-libc -print -ocode @PTEST_RESULT@/@PTEST_NAME@.pretty.c -then @PTEST_RESULT@/@PTEST_NAME@.pretty.c
 */

#include <stdio.h>

int main() {
  printf("");
}
