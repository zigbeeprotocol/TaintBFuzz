/* run.config
   COMMENT: Test non built-in `fread` memory tracking
*/

#include <stdio.h>

int main() {
  int buf[6];
  FILE *f = fopen("/dev/urandom", "r");
  // we assume this fopen will always succeed,
  // to ensure the code below is always tested
  int res = fread(buf + 1, sizeof(int), 4, f);
  //@ assert !\initialized(&buf[0]);
  if (res == 0) {
    //@ assert !\initialized(&buf[1]);
  }
  if (res >= 1) {
    //@ assert \initialized(&buf[1]);
  }
  if (res >= 2) {
    //@ assert \initialized(&buf[2]);
  }
  if (res >= 3) {
    //@ assert \initialized(&buf[3]);
  }
  if (res >= 4) {
    //@ assert \initialized(&buf[4]);
  }
  //@ assert !\initialized(&buf[5]);

  // intentionally do not read the return value;
  // but we suppose in this test that it will always succeed
  // and read 4 elements
  int buf2[6];
  fread(buf2 + 1, sizeof(int), 4, f);
  //@ assert !\initialized(&buf2[0]);
  //@ assert \initialized(&buf2[1..4]);
  //@ assert !\initialized(&buf2[5]);
  return 0;
}
