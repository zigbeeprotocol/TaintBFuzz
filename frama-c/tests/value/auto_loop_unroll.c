/* run.config*
   STDOPT: +"-eva-auto-loop-unroll 10"
   STDOPT: +"-eva-auto-loop-unroll 128"
*/

/* Tests the automatic loop unrolling heuristic. */

#include <__fc_builtin.h>

volatile int undet;

int g = 0;
void incr_g () {
  g++;
}

int incr (int i) {
  return i+1;
}

void simple_loops () {
  int res = 0;
  /* This loop should be automatically unrolled on the second run. */
  for (int i = 0; i < 100; i++) {
    res++;
  }
  Frama_C_show_each_auto(res);
  res = 0;
  /* This loop should not be automatically unrolled. */
  for (int i = 0; i < 1000; i++) {
    res++;
  }
  Frama_C_show_each_imprecise(res);
  res = 0;
  /* The annotation has priority over the automatic loop unrolling:
     this loop should never be unrolled. */
  /*@ loop unroll 0; */
  for (int i = 0; i < 100; i++) {
    res++;
  }
  Frama_C_show_each_imprecise(res);
  res = 0;
  /* The annnotation has priority over the automatic loop unrolling:
     this loop should always be unrolled. */
  /*@ loop unroll 100; */
  for (int i = 0; i < 100; i++) {
    res++;
  }
  Frama_C_show_each_singleton(res);
}

/* Examples of various loops that should be automatically unrolled
   on the second run, but not on the first. */
void various_loops () {
  int res = 0;
  /* Decreasing loop counter. */
  for (int i = 64; i > 0; i--)
    res++;
  Frama_C_show_each_64(res);
  res = 0;
  /* Decrements the loop counter by 3. */
  for (int i = 120; i > 0; i -= 3)
    res++;
  Frama_C_show_each_40(res);
  res = 0;
  /* Several increments of the loop counter. */
  for (int i = 0; i < 160; i++) {
    i += 2;
    res++;
    i--;
  }
  Frama_C_show_each_80(res);
  res = 0;
  /* Random increments of the loop counter. */
  for (int i = 0; i < 160;) {
    res++;
    if (undet)
      i += 2;
    else
      i += 5;
  }
  Frama_C_show_each_32_80(res);
  res = 0;
  /* More complex loop condition. */
  int x = 24;
  int k = Frama_C_interval(0, 10);
  for (int i = 75; i + x > 2 * k; i -= 2)
    res++;
  Frama_C_show_each_40_50(res);
  res = 0;
  /* Global loop counter. */
  for (g = 0; g < 101; g++) {
    res++;
  }
  Frama_C_show_each_101(res);
  res = 0;
  /* Loop calling some functions that do not modify the loop counter. */
  for (int i = 0; i < 25; i++) {
    incr_g();
    int t = incr(i);
    res = incr(res);
  }
  Frama_C_show_each_25(res);
  res = 0;
  /* Nested loops. */
  res = 0;
  for (int i = 0; i < 16; i++) {
    for (int j = 0; j < i; j++) {
      res++;
    }
  }
  Frama_C_show_each_120(res);
  res = 0;
  /* Loop counter modified on both sides of a conditional statement. */
  for (int i = 0; i < 64;) {
    if (undet)
      i++;
    else
      i+=2;
    res++;
  }
  Frama_C_show_each_32_64(res);
  res = 0;
  /* Loop counter decremented or directly assigned. */
  for (int i = 28; i > 0;) {
    if (undet)
      i = -1; // exits the loop
    else
      i--;
    res++;
  }
  Frama_C_show_each_1_28(res);
  res = 0;
  for (int i = 28; i > 0;) {
    if (undet)
      i = 2; // stay in the loop
    else
      i--;
    res++;
  }
  Frama_C_show_each_top(res);
  res = 0;
}

/* Loops that cannot be unrolled. */
void complex_loops () {
  /* Loop counter modified through a pointer. */
  int res = 0;
  int i = 0;
  int j = 0;
  int *p = &j;
  while (j < 64) {
    (*p)++;
    res++;
  }
  Frama_C_show_each_imprecise(res);
  /* Loop counter modified within a nested loop. */
  res = 0;
  i = 0;
  while (i < 64) {
    for (int j = 0; j < i; j++) {
      if (undet && i < 64)
        i++; // The outer loop could be unrolled, as this speeds up convergence.
    }
    res++;
    i++;
  }
  Frama_C_show_each_imprecise(res);
  res = 0;
  i = 0;
  while (i < 64) {
    for (int j = 0; j < i; j++) {
      if (undet && i > 0)
        i--; // The outer loop cannot be unrolled.
    }
    res++;
    i++;
  }
  Frama_C_show_each_imprecise(res);
  /* Loop counter incremented under a condition. */
  res = 0;
  i = 0;
  while (i < 10) {
    if (undet)
      i++;
    res++;
  }
  Frama_C_show_each_imprecise(res);
  res = 0;
  /* Loop counter modified by a function. */
  g = 0;
  while (g < 64) {
    incr_g();
    g++;
    res++;
  }
  Frama_C_show_each_imprecise(res);
  res = 0;
  /* Too complex loop condition. */
  int t[10] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};
  i = 0;
  while (t[i] < 6) {
    i++;
    res++;
  }
  Frama_C_show_each_imprecise(res);
  res = 0;
  /* Random loop condition. */
  i = 0;
  while (i < 64 || undet) {
    i++;
    res++;
  }
  Frama_C_show_each_imprecise(res);
}

/* Examples of loops with other exit conditions than simple comparisons.
   All loops could be automatically unrolled on the second run, but should
   not be unrolled on the first run. */
void various_conditions () {
  int i, res = 0;
  /* Exit conditions using equality. */
  for (i = 11; i; i--) {
    res++;
  }
  Frama_C_show_each_11(res);
  res = 0;
  for (i = 0; i != 12; i++) {
    res++;
  }
  Frama_C_show_each_12(res);
  res = 0;
  /* Loops with conjonction of exit conditions. */
  for (int i = 13 ; i-- && undet; ) {
    res ++;
  }
  Frama_C_show_each_0_13(res);
  res = 0;
  for (int i = 14 ; undet && i-- ; ) {
    res ++;
  }
  Frama_C_show_each_0_14(res);
  res = 0;
  /* Loops with several exit conditions. */
  for (int i = 0 ; undet ; i++) {
    if (undet || i >= 15)
      break;
    res ++;
  }
  Frama_C_show_each_0_15(res);
  res = 0;
  for (int i = 0; i < 111; i++) {
    res++;
    if (undet && res > 10)
      break;
  }
  Frama_C_show_each_11_111(res);
  res = 0;
  /* Exit conditions using pointers. */
  int x = 16;
  int *p = &x;
  for (int i = 0 ; i < *p ; ++i) {
    res++;
  }
  Frama_C_show_each_16(res);
  res = 0;
}

/* Examples of loops where temporary variables are introduced by Frama-C.
   All loops could be automatically unrolled on the second run, but should
   not be unrolled on the first run. */
void temporary_variables () {
  int i, j = 0, k = 0, res = 0;
  for (i = 0; i++ < 20;) {
    res++;
  }
  Frama_C_show_each_20(res);
  res = 0;
  for (i = 21; i--;) {
    res++;
  }
  Frama_C_show_each_21(res);
  res = 0;
  for (i = 0; j < 21; i++) {
    j = i;
    res++;
  }
  Frama_C_show_each_22(res);
  res = 0;
  j = 0;
  for (i = 0; k < 22; i++) {
    j = i;
    k = j;
    res++;
  }
  Frama_C_show_each_23(res);
  res = 0;
  j = 0;
  for (i = 0; j < 23; i++) {
    if (undet)
      j = i;
    res++;
  }
  Frama_C_show_each_top(res);
}

/* Examples of natural loops with goto or continue statements. */
void loops_with_goto () {
  int i, res = 0;
  for (i = 0; i < 30; i++) {
    res++;
    if (undet)
      goto middle;
  }
  Frama_C_show_each_30(res);
  res = 0;
 middle: ;
  /* Can be unrolled, but [res] should still be imprecise. */
  for (i = 0; i < 31; i++) {
    res++;
    if (undet)
      goto middle;
  }
  Frama_C_show_each_top(res);
  res = 0;
  /* Should be unrolled, and [res] should be precise. */
  for (i = 0; i < 32; i++) {
    res++;
    if (undet)
      goto L1;
  L1:;
  }
  Frama_C_show_each_32(res);
  res = 0;
  /* Should be unrolled, but [res] should still be imprecise. */
  for (i = 0; i < 33; i++) {
  L2:res++;
    if (undet)
      goto L2;
  }
  Frama_C_show_each_33_inf(res);
  res = 0;
  /* Should never be unrolled. */
  for (i = 0; i < 34; res++) {
  L3:i++;
    if (undet)
      goto L3;
  }
  Frama_C_show_each_top(res);
  res = 0;
  /* Should be unrolled, and [res] should be precise. */
  for (i = 0; i < 35; i++) {
    if (undet)
      continue;
    res++;
  }
  Frama_C_show_each_0_35(res);
  res = 0;
  /* Should be unrolled, and [res] should be precise. */
  for (i = 36; i--; res++) {
    if (undet)
      continue;
  }
  Frama_C_show_each_36(res);
  res = 0;
  /* Should be unrolled, and [res] should be precise. */
  for (i = 0; i < 37; i++) {
    if (i < 10)
      continue;
    res++;
  }
  Frama_C_show_each_27(res);
  res = 0;
}

/* Examples of loops formed by goto statements. */
void non_natural_loops () {
  int i, res;
  res = 0;
  i = 0;
 loop1:
  i++;
  res++;
  if (i < 50) {
    goto loop1;
  }
  Frama_C_show_each_50(res);
  res = 0;
  i = 50;
 loop2:
  res++;
  if (undet && i--) {
    goto loop2;
  }
  Frama_C_show_each_1_51(res);
  res = 0;
}

/* Tests the automatic loop unrolling on loops that follow directly each other. */
void following_loops () {
  int i = 0, j = 0;
  while (i < 15) {
    i++;
    j++;
  }
  while (i < 30) {
    i++;
    j++;
  }
  Frama_C_show_each_30(j);
  i = 0;
  j = 0;
  while (i < 15 && undet) {
    i++;
    j++;
  }
  while (i < 30) {
    i++;
    j++;
  }
  /* The equality relation between [i] and [j] is lost between the two loops,
     where all states exiting the first loop are joined. However, the unrolling
     prevents the value of [j] to be completely imprecise. */
  Frama_C_show_each_30(j);
}

void main () {
  simple_loops ();
  various_loops ();
  complex_loops ();
  various_conditions ();
  temporary_variables ();
  loops_with_goto ();
  non_natural_loops ();
  following_loops ();
}
