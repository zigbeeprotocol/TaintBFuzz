#include <time.h>
#include <sys/utsname.h>

int main() {
  struct utsname n;
  int r = uname(&n);
  //@ assert \initialized(&n);
  return 0;
}
