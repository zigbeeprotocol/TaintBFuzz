/* run.config*
PLUGIN: @PTEST_PLUGIN@ metrics
   OPT: -eva-no-builtins-auto @EVA_OPTIONS@ @FRAMAC_SHARE@/libc/string.c -eva -eva-slevel 6 -metrics-eva-cover -then -metrics-libc
*/
#include "string.h"

void main() {
  char *s = "blabli";
  int l = strlen(s);
}
