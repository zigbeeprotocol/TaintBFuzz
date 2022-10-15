/* run.config
   CMD: @frama-c@ -eva -eva-no-results -mdr-gen sarif -mdr-sarif-deterministic
   LOG: with-libc.sarif
   OPT: -mdr-out @PTEST_RESULT@/with-libc.sarif
   LOG: without-libc.sarif
   OPT: -mdr-no-print-libc -mdr-out @PTEST_RESULT@/without-libc.sarif
*/

#include <string.h>

int main() {
  char *s = "hello world";
  int n = strlen(s);
  return n;
}
