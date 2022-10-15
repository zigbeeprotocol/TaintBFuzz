/* run.config
   DONTRUN: test run by main.c
*/

#include "for-list-functions2.h"
#include "for-list-functions.h"

static int static_fun() {
  static int init = 0;
  if (!init) {
    init = 1;
    return 2;
  }
  return 4;
}

void k() {
  /*@ loop unroll 10; */ // Eva is not loaded, so we must ignore the annotation
  for (int i = 0; i < 10; i++) {
    extf();
  }
}
