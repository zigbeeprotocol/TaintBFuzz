#include <signal.h>

void f() {
  signal (SIGUSR1, SIG_IGN);
  signal (SIGUSR2, SIG_ERR);
  signal (SIGUNUSED, SIG_DFL);
}
