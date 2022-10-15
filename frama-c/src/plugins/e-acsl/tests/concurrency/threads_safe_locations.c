#include <errno.h>
#include <pthread.h>
#include <stdio.h>

void *thread_start(void *arg) {
  //@ assert \valid(stdout) && \initialized(stdout);
  //@ assert \valid(stderr) && \initialized(stderr);
  //@ assert \valid(stdin) && \initialized(stdin);
  int *addrof_errno = &errno;
  //@ assert \valid(addrof_errno) && \initialized(addrof_errno);
  return NULL;
}

int main() {
  pthread_t t;
  pthread_create(&t, NULL, thread_start, NULL);
  pthread_join(t, NULL);
  return 0;
}
