#include "stdatomic.c"

void test_atomic_int() {
  atomic_int a = ATOMIC_VAR_INIT(42);
  int aa = 51;
  atomic_init(&a, 42);
  int c = kill_dependency(a);
  atomic_thread_fence(memory_order_relaxed);
  atomic_signal_fence(memory_order_consume);
  _Bool b1 = atomic_is_lock_free(&a);
  atomic_store(&a, 43);
  atomic_store_explicit(&a, 43, memory_order_release);
  int d = atomic_load(&a);
  int e = atomic_load_explicit(&a, memory_order_acquire);
  int f = atomic_exchange(&a, 44);
  int g = atomic_exchange_explicit(&a, 44, memory_order_acq_rel);
  _Bool b2 = atomic_compare_exchange_strong(&a, &aa, 45);
  _Bool b3 = atomic_compare_exchange_strong_explicit(&a, &aa, 46,
                                                     memory_order_seq_cst,
                                                     memory_order_relaxed);
  _Bool b4 = atomic_compare_exchange_weak(&a, &aa, 47);
  _Bool b5 = atomic_compare_exchange_weak_explicit(&a, &aa, 48,
                                                   memory_order_consume,
                                                   memory_order_relaxed);
  int add1 = atomic_fetch_add(&a, 60);
  int add2 = atomic_fetch_add_explicit(&a, 61, memory_order_acquire);
  int sub1 = atomic_fetch_sub(&a, 62);
  int sub2 = atomic_fetch_sub_explicit(&a, 63, memory_order_acquire);
  int or1 = atomic_fetch_or(&a, 64);
  int or2 = atomic_fetch_or_explicit(&a, 65, memory_order_acquire);
  int xor1 = atomic_fetch_xor(&a, 66);
  int xor2 = atomic_fetch_xor_explicit(&a, 67, memory_order_acquire);
  int and1 = atomic_fetch_and(&a, 68);
  int and2 = atomic_fetch_and_explicit(&a, 69, memory_order_acquire);
  atomic_flag flag = ATOMIC_FLAG_INIT;
  _Bool b6 = atomic_flag_test_and_set(&flag);
  _Bool b7 = atomic_flag_test_and_set_explicit(&flag, memory_order_relaxed);
  atomic_flag_clear(&flag);
  atomic_flag_clear_explicit(&flag, memory_order_relaxed);
}

void test_atomic_pointer() {
}

void main() {
  test_atomic_int();
}
