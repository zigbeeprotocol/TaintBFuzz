/* run.config
  COMMENT: does not check RTE plugin!
  PLUGIN: @EVA_PLUGINS@
  OPT: @EVA_TEST@
*/
#include <stddef.h>

size_t fsize3(int n) {
  char b[n + 3]; // variable length array
  return sizeof b; // execution time sizeof
}

int main() {
  return fsize3(5);
}
