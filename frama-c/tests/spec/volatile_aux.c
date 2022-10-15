/* run.config
   DONTRUN: main test file is volatile.c
*/

#include "volatile.h"

int f (int x) {
  x++;
  v = x;
  return v+x;
}
