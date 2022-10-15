#include <pthread.h>
#include <stdlib.h>

#define SIZE 10

int *values[SIZE];

void *write_value(void *arg) {
  int idx = *(int *)arg;
  values[idx] = malloc(sizeof(int));
  *values[idx] = idx;
  return NULL;
}

void *read_value(void *arg) {
  int idx = *(int *)arg;
  //@ assert *values[idx] == idx;
  free(values[idx]);
  return NULL;
}

int main() {
  pthread_t t;
  int args[SIZE];

  for (int i = 0; i < SIZE; ++i) {
    args[i] = i;
    pthread_create(&t, NULL, write_value, &args[i]);
    pthread_join(t, NULL);
  }
  for (int i = 0; i < SIZE; ++i) {
    pthread_create(&t, NULL, read_value, &args[i]);
    pthread_join(t, NULL);
  }

  return 0;
}
