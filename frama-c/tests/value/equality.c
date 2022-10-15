/* run.config*
   STDOPT: +"-eva-domains equality -eva-warn-copy-indeterminate=-assign_by_copy"
*/

/* Tests for the equality domain. */

#include <__fc_builtin.h>
#include <math.h>

volatile int rand;

/* Tests the replacement of an lvalue x by an equal term when x also appears
   in another term t equal to x. The precision gain is useless in these cases,
   but the domain nust not crash or be unsound: x cannot be replaced by t. */
void replace_lvalue () {
  int x = rand;
  int y = x;
  int z = 0;
  /* Tests if x is even in a way that the backward propagation fails to
     reduce x. */
  if (x == x/2 + x/2) {
    /* Replaces x by y (and not by x/2 + x/2) in the equality domain.  */
    x = 0;
    /* After the test, the equality could further reduce y to [-8..8]. */
    if (-10 < y && y < 10) {
      /* A temporary variable is needed to avoid a cycle in the evaluations:
         when evaluating y, the oracle for y/2+y/2 is top (as y has not been
         evaluated yet). */
      int tmp = y;
      z = tmp;
    }
  }
}

/* Tests the equality domain on assignments by copy of indeterminate values.
   These indeterminate values must not be reduced when using the equalities. */
void assign_by_copy () {
  int x;
  if (rand)
    x = Frama_C_interval(0, 42);
  int y = x; // x may be not initialized but is copied, so no alarm
  int w = y; /* the equality {y = x} could be used, but x must not be reduced
                x and y may be not initialized. */
  int z = x + 1; // x may still be not initialized: alarm
}


/* A pattern found in a case study that can be solved with both the
   equality domain and the symbolic locations domain. */
void symbolic () {
  float f, g, tmp, res;
  f = Frama_C_float_interval(0.f, 10.f);
  g = Frama_C_float_interval(0.f, 10.f);
  tmp = f - g;
  if (tmp > 0.) {
    tmp = 0.;
    res = sqrtf(f-g); // requires f-g positive
  }
}

void main () {
  replace_lvalue ();
  assign_by_copy ();
  symbolic ();
}
