/* run.config
   COMMENT: test assertion failure without printing assertion data

   STDOPT: #"-e-acsl-no-assert-print-data"
*/
/* run.config_dev
   MACRO: ROOT_EACSL_GCC_OPTS_EXT --no-assert-print-data
*/

#include <limits.h>

int main() {
  int value = INT_MAX;
  //@ check \let x = value; \false;
  return 0;
}
