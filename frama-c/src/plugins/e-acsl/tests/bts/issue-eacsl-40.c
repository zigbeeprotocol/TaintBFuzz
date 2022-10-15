/* run.config
   COMMENT: frama-c/e-acsl#40, test for initialized memory after a call to fread
   on /dev/urandom.
*/

#include <stdio.h>

int main() {
  char buf[4];
  FILE *f = fopen("/dev/urandom", "r");
  if (f) {
    char buf[4];
    int res = fread(buf, 1, 4, f);
    if (res == 4) {
      //@ assert \initialized(&buf[3]);
      buf[0] = buf[3];
    } else
      return 2;
  } else
    return 1;
  return 0;
}
