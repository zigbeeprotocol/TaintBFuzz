/* run.config
DONTRUN: main test is at %{dep:@PTEST_DIR@/typedef_multi_1.c}
*/

#include "typedef_multi.h"

void g() { 
  /*@ loop invariant x<=(3+2); */ 
  while (x<y) x++; }
