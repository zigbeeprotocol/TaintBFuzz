/*run.config
  STDOPT: #"-kernel-msg-key printer:field-offsets"
 */

#include <stdlib.h>

struct st {
  int a;
  char b;
  void *p;
};

struct fam {
  int a;
  char b;
  int fam[]; // check that the printer handles flexible arrays members
};

int main() {
  struct st st1 = { 2 };
  struct fam *fam = malloc(sizeof(fam) + sizeof(int)*10);
  fam->fam[9] = 0;
  return st1.b + fam->fam[9];
}
