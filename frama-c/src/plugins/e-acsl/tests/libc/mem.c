/* run.config
   COMMENT: Test non built-in `memset`, `memcpy` and `memmove` memory tracking
*/

#include <string.h>

int main() {
  char a[2];
  memset(a, 1, 1);
  //@assert \initialized(&a[0]);
  //@assert !\initialized(&a[1]);
  memset(a + 1, 1, 1);
  //@assert \initialized(&a[1]);
  int b[5];
  memset(&b[2], 42, 2 * sizeof(b[0]));
  //@assert !\initialized(&b[0]);
  //@assert !\initialized(&b[1]);
  //@assert \initialized(&b[2..3]);
  //@assert !\initialized(&b[4]);

  char c[4];
  memcpy(c + 1, a, 2);
  //@assert !\initialized(&c[0]);
  //@assert \initialized(&c[1..2]);
  //@assert !\initialized(&c[3]);

  memmove(c, c + 1, 2);
  //@ assert \initialized(&c[0..2]);
  //@ assert !\initialized(&c[3]);
}
