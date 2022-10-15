/* run.config
   COMMENT: Test non built-in `sprintf` memory tracking
*/

#include <stdio.h>

int main() {
  {
    char buf[4];
    //@ assert !\initialized(&buf[0..3]);

    sprintf(buf, "%d", 10);
    //@ assert \initialized(&buf[0..2]);
    //@ assert !\initialized(&buf[3]);
  }
  { // snprintf with n < what would be printed
    char buf[4];
    //@ assert !\initialized(&buf[0..3]);

    snprintf(buf, 2, "%d", 10);
    //@ assert \initialized(&buf[0..1]);
    //@ assert !\initialized(&buf[2..3]);
  }
  { // snprintf with n >= what would be printed
    char buf[4];
    //@ assert !\initialized(&buf[0..3]);

    snprintf(buf, 4, "%d", 10);
    //@ assert \initialized(&buf[0..2]);
    //@ assert !\initialized(&buf[3]);
  }
  return 0;
}
