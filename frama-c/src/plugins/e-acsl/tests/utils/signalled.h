#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#define STRINGIFY(x) #x
#define TOSTRING(x)  STRINGIFY(x)
#ifndef __FRAMAC__
#  define __FC_FILENAME__ __FILE__
#endif
#define AT __FC_FILENAME__ ":" TOSTRING(__LINE__)

int testno = 0;

void signal_eval(int status, int expect_signal, const char *at) {
  fprintf(stderr, "TEST %d: ", ++testno);
  int signalled = WIFSIGNALED(status);
  if (signalled && expect_signal)
    fprintf(stderr, "OK: Expected signal at %s\n", at);
  else if (!signalled && !expect_signal)
    fprintf(stderr, "OK: Expected execution at %s\n", at);
  else if (!signalled && expect_signal) {
    fprintf(stderr, "FAIL: Unexpected execution at %s\n", at);
    exit(1);
  } else if (signalled && !expect_signal) {
    fprintf(stderr, "FAIL: Unexpected signal at %s\n", at);
    exit(2);
  }
}

/* The following macro runs a chunk of code in a subprocess and evaluates
   the result. This macro assumes that fork is always successful. */
#define SIGNALLED_AT(code, expect_signal, at)                                  \
  {                                                                            \
    pid_t pid = fork();                                                        \
    if (!pid) {                                                                \
      code;                                                                    \
      exit(0);                                                                 \
    } else {                                                                   \
      int process_status;                                                      \
      waitpid(pid, &process_status, 0);                                        \
      signal_eval(process_status, expect_signal, at);                          \
    }                                                                          \
  }

#define ABRT(code)        SIGNALLED_AT(code, 1, AT)
#define OK(code)          SIGNALLED_AT(code, 0, AT);
#define ABRT_AT(code, at) SIGNALLED_AT(code, 1, at)
#define OK_AT(code, at)   SIGNALLED_AT(code, 0, at)
