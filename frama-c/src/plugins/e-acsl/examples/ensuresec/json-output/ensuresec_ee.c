// Get default definitions and macros, e.g. pthread_rwlock_t
#ifndef _DEFAULT_SOURCE
#  define _DEFAULT_SOURCE 1
#endif

#include <assert.h>
#include <errno.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

// Number of writers and readers created
#define SIZE 10

// Mutex protecting the calls to `rand()`
static pthread_mutex_t rand_mutex;

// Data array
static int *values[SIZE];

// Synchronization array: if `written[idx] == 1` then `values[idx]` has been written to.
static int written[SIZE] = {0};

// Read-write lock protecting the accesses to `written`
static pthread_rwlock_t locks[SIZE];

// Thread-safe version of `rand()` that returns a random value between `min`
// and `max`.
/*@ requires 0 <= min < max <= RAND_MAX;
  @ ensures min <= \result <= max; */
static int ensuresec_rand(int min, int max) {
  pthread_mutex_lock(&rand_mutex);
  int value = rand();
  pthread_mutex_unlock(&rand_mutex);
  return (double)value * (max - min) / RAND_MAX + min;
}

/*@ requires \let idx = *(int*)arg; 0 <= idx < SIZE; */
static void *write_value(void *arg) {
  int idx = *(int *)arg;
  pthread_rwlock_t *lock = &locks[idx];

  // Acquire a read lock so that the specification can check `writte[idx]` and
  // `values[idx]`.
  pthread_rwlock_rdlock(lock);

  /*@ requires written[idx] == 0;
    @ ensures written[idx] == 1;
    @ ensures \valid_read(values[idx]) && \initialized(values[idx]); */
  {
    // Long computation
    int duration = ensuresec_rand(1, 5);
    sleep(duration);

    // No data race since each thread will access its own index and
    // `read_value()` will not read this index until we update `written[idx]`.
    values[idx] = malloc(sizeof(int));
    *values[idx] = idx + duration;

    // Now we want to update `written[idx]` so we need to acquire the lock for
    // this index in writing mode
    pthread_rwlock_unlock(lock);
    pthread_rwlock_wrlock(lock);
    written[idx] = 1;
  }

  pthread_rwlock_unlock(lock);
  return NULL;
}

/*@ requires \let idx = *(int*)arg; 0 <= idx < SIZE; */
static void *read_value(void *arg) {
  int idx = *(int *)arg;
  pthread_rwlock_t *lock = &locks[idx];

  // Long computation
  int duration = ensuresec_rand(0, 3);
  sleep(duration);

  // Check `written[idx]` while the value is 0
  int idx_written;
  do {
    pthread_rwlock_rdlock(lock);
    idx_written = written[idx];
    // Unlock and sleep a bit between each check to let `write_value()` some
    // time to change the value of `written[idx]`
    pthread_rwlock_unlock(lock);
    usleep(100);
  } while (!idx_written);

  // Acquire a read lock so that the specification can check `written[idx]` and
  // `values[idx]`.
  pthread_rwlock_rdlock(lock);
  /*@ requires written[idx] == 1;
    @ requires \valid_read(values[idx]) && \initialized(values[idx]); */
  {
    int value = *values[idx];
    free(values[idx]);

    // Non-critical assertion that will sometimes fail and raise an alert
    //@ check (value - idx) > duration;
  }
  pthread_rwlock_unlock(lock);

  return NULL;
}

int main() {
  pthread_t writers[SIZE];
  pthread_t readers[SIZE];
  int args[SIZE];

  // Initialize rand seed
  srand(time(NULL));

  // Initialize locks
  int res = pthread_mutex_init(&rand_mutex, NULL);
  assert(res == 0);
  for (int i = 0; i < SIZE; ++i) {
    res = pthread_rwlock_init(&locks[i], NULL);
    assert(res == 0);
  }

  // Create all threads
  for (int i = 0; i < SIZE; ++i) {
    args[i] = i;
    pthread_create(&writers[i], NULL, write_value, &args[i]);
    pthread_create(&readers[i], NULL, read_value, &args[i]);
  }

  // Wait for completion
  for (int i = 0; i < SIZE; ++i) {
    pthread_join(writers[i], NULL);
    pthread_join(readers[i], NULL);
  }

  return 0;
}
