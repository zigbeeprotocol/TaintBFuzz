/* run.config
  STDOPT: #"-e-acsl-full-mtracking"
*/
/* run.config_dev
  MACRO: ROOT_EACSL_GCC_OPTS_EXT --full-mtracking --rt-debug
*/

#include <time.h>

int main() {
  // On linux x32 and x64, the time() function comes from the vdso segment
  time_t tmp = time(NULL);
  //@ assert tmp != -1;
  return 0;
}
