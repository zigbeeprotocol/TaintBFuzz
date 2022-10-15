/* run.config*
   STDOPT: #"%{dep:@PTEST_DIR@/abstract_struct_2.c} -lib-entry -eva-msg-key initial-state"
*/
#include "stdlib.h"

struct abstracttype;
struct something {
  struct abstracttype *data;
};
static struct something *repositories;

void main(void) {
  repositories = calloc(1, sizeof(struct something));
}
