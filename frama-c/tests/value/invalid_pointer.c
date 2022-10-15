/* run.config*
  STDOPT: +"-warn-invalid-pointer -absolute-valid-range=10-30"
  STDOPT: +"-no-warn-invalid-pointer -absolute-valid-range=10-30"
*/

#include <__fc_builtin.h>
#include <stdint.h>
#include <signal.h>

/* Tests the emission of \object_pointer alarms when -warn-invalid-pointer
   is enabled. The second run should emit no alarm. */

volatile int undet;

/* Simple pointer computations. */
void pointer_computation () {
  int x;
  int *p = &x;
  if (undet)
    p--; // Red alarm.
  p++; // No alarm.
  if (undet)
    p++; // Red alarm.
  int i = undet;
  p += i; // Unknown alarm. [i] should be reduced to {-1, 0}.
  int j = undet;
  p -= j; // Unknown alarm. [j] should be reduced to {-1, 0, 1}.
  p --;   // Unknown alarm. [p] should be exactly {&x}.
  int array[25];
  int *q = undet ? &x : &array[0];
  int offset1 = Frama_C_interval(0, 10);
  q += offset1; // Unknown alarm. [offset1] should not be reduced.
  int offset2 = Frama_C_interval(0, 50);
  q += offset2; // Unknown alarm. [offset2] should be reduced to [0..25].
  q += 0; // No alarm.
}

/* Increment or decrement pointers in loops. */
void pointer_in_loops () {
  int t[128];
  int *p = &t[0];
  /*@ loop unroll 128; */
  for (int i = 0; i < 128; i++) {
    *p = i;
    p++; // No alarm.
  }
  if (undet) {
    int *q = &t[127];
    /*@ loop unroll 128; */
    for (int i = 0; i < 128; i++) {
      *q = i;
      q--; // Alarm in the last iteration: q points to t[-1].
    }
    Frama_C_show_each_bottom(q); // Should not be reached.
  }
}

/* Conversion integer -> pointer. */
void int_conversion () {
  int x, *p;
  p = (int *)0; // NULL pointer: always ok.
  p = (int *) 20; // Inside -absolute-valid-range: no alarms.
  if (undet) {
    p = (int *) 42; // Outside -absolute-valid-range: red alarm.
  }
  x = Frama_C_interval(15, 25);
  p = (int *) x; // Inside -absolute-valid-range: no alarms.
  x = Frama_C_interval(100, 500);
  if (undet) {
    p = (int *) x; // Outside -absolute-valid-range: red alarm.
  }
  x = Frama_C_interval(15, 100);
  p = (int *) x;     // Unknown alarm. [x] should be reduced to [15..31].
  p = (int *) undet; // Unknown alarm. [p] should be have value in [0..31].
}

void addrof () {
  int a[10], *p;
  p = &(a[0]);
  p = &(a[10]);
  if (undet)
    p = &(a[11]); // Invalid alarm
  if (undet)
    p = &(a[-1]); // Invalid alarm
  int offset = undet;
  p = &(a[offset]); /* Unknown alarm. [offset] should be reduced to [0..10]. */
}

typedef union {
  uintptr_t integer;
  int *pointer;
} ptr_union;

/* Creates invalid pointers through an union. */
void union_pointer () {
  int *p;
  ptr_union u;
  u.integer = 0;
  p = u.pointer; // No alarm.
  if (undet) {
    u.integer = 42;
    p = u.pointer; // Red alarm.
  }
  u.integer = undet;
  p = u.pointer; // Unknown alarm. [u.integer] should be reduced to [0..31].
}

/* Creates invalid pointers through untyped writes. */
void write_pointer () {
  int x;
  int *p = 0;
  *((uintptr_t *) &p) = &x;
  int *q = p; // No alarm.
  *((uintptr_t *) &p) = (uintptr_t)p + undet;
  q = p; // Unknown alarm.
  *((uintptr_t *) &p) = 42;
  if (undet) {
    q = p; // Red alarm.
  }
}

/* Tests the evaluation of the logical predicate \object_pointer when
   -warn-invalid-pointer is disabled. */
void object_pointer_predicate () {
  int x, array[64];
  int *p = &x;
  /*@ assert \object_pointer(p); */
  if (undet) {
    p--;
    /*@ assert \object_pointer(p); */
  }
  p++;
  /*@ assert \object_pointer(p); */
  if (undet) {
    p++;
    /*@ assert \object_pointer(p); */
  }
  p += undet;
  /*@ assert \object_pointer(p); */
  /*@ assert \object_pointer(p); */
  Frama_C_show_each_object_pointer(p);
  p = (int *)((uintptr_t)&x + undet);
  /*@ assert \object_pointer(p); */
  /*@ assert \object_pointer(p); */
  Frama_C_show_each_object_pointer_char(p);
  int i = Frama_C_interval(0, 20);
  p = undet ? &x : &array[i];
  /*@ assert \object_pointer(p); */
  p += i;
  /*@ assert \object_pointer(p); */
  p += undet;
  /*@ assert \object_pointer(p); */
  Frama_C_show_each_object_pointer_array(p);
  p = (int *) 0;
  /*@ assert \object_pointer(p); */
  if (undet)
    p = (int *) 20;
  /*@ assert \object_pointer(p); */
  if (undet)
    p = (int *) 50;
  /*@ assert \object_pointer(p); */
  p = (int *) undet;
  /*@ assert \object_pointer(p); */
  if (undet) {
    p = (int *) 100;
    /*@ assert \object_pointer(p); */
  }
}

/* CERT C UB 62. An attempt is made to access, or generate a pointer to just
   past, a flexible array member of a structure when the referenced object
   provides no elements for that array (6.7.2.1). */
struct sfam {
  int len;
  char fam[];
};

void flexible_array_member() {
  struct sfam s1 = { 0 };
  if (undet) {
    char *p = s1.fam + 1; // UB 62 (generate a pointer ...)
  }
  if (undet) {
    char *p = s1.fam;
    *(p+1) = 0; // UB 62 (access a pointer ...)
  }
}

void main () {
  pointer_computation ();
  pointer_in_loops ();
  int_conversion ();
  addrof ();
  union_pointer ();
  write_pointer ();
  object_pointer_predicate ();
  flexible_array_member();
   // should not emit an alarm
  signal (SIGUSR1, SIG_IGN);
  signal (SIGUSR2, SIG_ERR);
  signal (SIGUNUSED, SIG_DFL);
}
