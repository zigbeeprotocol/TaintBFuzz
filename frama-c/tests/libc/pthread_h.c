#define _GNU_SOURCE // if you want to compile with GCC
#include <pthread.h>
#include <stdio.h>

int retval;

void *start_routine(void *arg) {
  printf("inside start_routine\n");
  retval = *(int*)arg + 1;
  return &retval;
}

volatile int v;
int main() {
  pthread_t thread;
  int thread_arg = 42;
  int r = pthread_create(&thread, 0, start_routine, &thread_arg);
  if (r) {
    printf("pthread_create failed\n");
    return 1;
  }
  printf("pthread_create succeeded\n");
  r = pthread_setname_np(thread, "not very long");
  if (r) return 1;
  char buf[16];
  r = pthread_getname_np(thread, buf, (size_t)16);
  printf("name: %s\n", buf);
  if (r) return 1;
  int *retv;
  #ifdef __FRAMAC__
  // "Simulate" execution of the thread with Eva, without Mthread
  retv = start_routine(&thread_arg);
  #endif
  r = pthread_join(thread, (void **)&retv);
  if (r) {
    printf("pthread_join failed\n");
    return 1;
  }
  printf("pthread_join succeeded, retval = %d\n", *retv);
  return 0;
}
