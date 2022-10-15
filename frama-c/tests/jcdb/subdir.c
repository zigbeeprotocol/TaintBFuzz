/* run.config
   NOFRAMAC:
   DEPS: subdir1/header.h subdir2/included.h subdir.json subdir.c included2.h
   EXECNOW: LOG subdir.res LOG subdir.err (cd subdir1 && @frama-c@ -add-symbolic-path $PWD/..:PWD/.. -json-compilation-database ../subdir.json ../subdir.c) > @PTEST_RESULT@/subdir.res 2> @PTEST_RESULT@/subdir.err
*/

// this test must be run with PWD in subdir1
#include "subdir1/header.h"
#include "included.h" // in subdir2, via '-Isubdir2' in subdir.json
#include "__fc_builtin.h" // to check that Frama-C's libc is correctly included

int main() {
  return ONE + TWO + THREE;
}
