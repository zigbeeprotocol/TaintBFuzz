#include <errno.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#define SIZE 10

int *values[SIZE];

int write_count = 0;
int read_count = 0;
pthread_cond_t write_cond, read_cond;
pthread_mutex_t write_mutex, read_mutex;

#define WAIT_UNTIL_CONDVAR(count_var, mutex_var)                               \
  do {                                                                         \
    int res = pthread_mutex_trylock(&mutex_var);                               \
    if (res == 0) {                                                            \
      int done = count_var == SIZE;                                            \
      pthread_mutex_unlock(&mutex_var);                                        \
      if (done) {                                                              \
        break;                                                                 \
      }                                                                        \
    } else if (res != EBUSY) {                                                 \
      perror("Unable to lock " #mutex_var);                                    \
    }                                                                          \
    usleep(100);                                                               \
  } while (1)

/*@ ensures \let idx = *(int*)arg;
            \valid(values[idx]) && \initialized(values[idx]); */
void *write_value(void *arg) {
  if (pthread_mutex_lock(&write_mutex) != 0) {
    perror("Unable to lock mutex in write_value()");
    exit(1);
  }
  ++write_count;
  if (pthread_cond_wait(&write_cond, &write_mutex) != 0) {
    perror("Unable to wait on condvar in write_value()");
    exit(1);
  }
  if (pthread_mutex_unlock(&write_mutex) != 0) {
    perror("Unable to unlock mutex in write_value()");
    exit(1);
  }
  usleep(100);

  int idx = *(int *)arg;
  values[idx] = malloc(sizeof(int));
  *values[idx] = idx;
  return NULL;
}

/* The checks `\valid(values[idx])` and `\initialized(values[idx])` fail because
 * even if `read_value()` waits for ̀write_value()` to be finished before
 * reading the value, the generated code will check the specification before
 * calling `read_value()`, where we do not know if `write_value()` is finished.
 */
/*@ requires !(\let idx = *(int*)arg;
               \valid_read(values[idx]) && \initialized(values[idx])); */
void *read_value(void *arg) {
  if (pthread_mutex_lock(&read_mutex) != 0) {
    perror("Unable to lock mutex in read_value()");
    exit(1);
  }
  ++read_count;
  if (pthread_cond_wait(&read_cond, &read_mutex) != 0) {
    perror("Unable to wait on condvar in read_value()");
    exit(1);
  }
  if (pthread_mutex_unlock(&read_mutex) != 0) {
    perror("Unable to unlock mutex in read_value()");
    exit(1);
  }
  usleep(100);

  /* The contract can instead be written here so that the synchronisation
   * between `read_value()` and `write_value()` is done before evaluating the
   * specification. */
  /*@ requires \let idx = *(int*)arg;
               \valid_read(values[idx]) && \initialized(values[idx]); */
  {
    int idx = *(int *)arg;
    //@ assert *values[idx] == idx;
    free(values[idx]);
    return NULL;
  }
}

int main() {
  pthread_t writers[SIZE];
  pthread_t readers[SIZE];
  int args[SIZE];

  if (pthread_mutex_init(&write_mutex, NULL) != 0) {
    perror("Unable to initialize write mutex");
    exit(1);
  }
  if (pthread_cond_init(&write_cond, NULL) != 0) {
    perror("Unable to initialize write cond var");
    exit(1);
  }
  if (pthread_mutex_init(&read_mutex, NULL) != 0) {
    perror("Unable to initialize read mutex");
    exit(1);
  }
  if (pthread_cond_init(&read_cond, NULL) != 0) {
    perror("Unable to initialize read cond var");
    exit(1);
  }

  // Create all threads
  for (int i = 0; i < SIZE; ++i) {
    args[i] = i;
    pthread_create(&writers[i], NULL, write_value, &args[i]);
    pthread_create(&readers[i], NULL, read_value, &args[i]);
  }

  // Wait for every thread to be waiting on their condvar
  WAIT_UNTIL_CONDVAR(write_count, write_mutex);
  WAIT_UNTIL_CONDVAR(read_count, read_mutex);

  // Wake up writers and wait for completion
  if (pthread_cond_broadcast(&write_cond) != 0) {
    perror("Unable to broadcast to write cond var");
    exit(11);
  }
  for (int i = 0; i < SIZE; ++i) {
    pthread_join(writers[i], NULL);
  }

  // Wake up readers and wait for completion
  if (pthread_cond_broadcast(&read_cond) != 0) {
    perror("Unable to broadcast to read cond var");
    exit(12);
  }
  for (int i = 0; i < SIZE; ++i) {
    pthread_join(readers[i], NULL);
  }

  return 0;
}
