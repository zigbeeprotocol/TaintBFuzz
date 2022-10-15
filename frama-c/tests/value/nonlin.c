/* run.config*
   STDOPT: +"-eva-subdivide-non-linear 14 -eva-subdivide-non-linear-function=local_subdivide:32 -eva-msg-key nonlin"
*/

#include "__fc_builtin.h"

volatile int v; volatile short vs;

/* Checks that the subdivision does not fail when pointer values get involved. */
void subdivide_pointer () {
  int y = 17;
  int x = Frama_C_interval(-10, 10);
  int *p = &x;
  int i = Frama_C_interval(0,100);
  /* The complete expression is a pointer: no subdivision. */
  int *q = p + i - i;
  /* The complete expression is a singleton: no subdivision. */
  y = *(&y + i - i);
  /* The complete expression is an imprecise integer: subdivision (but no
     reduction, as it cannot improve the bounds of the result). */
  y = *(p + i - i);
  /* The subexpression contains a pointer, but the complete expression is an
     integer, and the subdivision can reduce its value. */
  int t[10] = {0, 1, 2, 4, 5, 6, 7, 8, 9};
  p = &t[0];
  i = Frama_C_interval(0, 10);
  y = *(p + i - i);
  /* The splitted lvalue contains a pointer value: no subdivision. */
  i = v ? i : (int) &x;
  y = *(p + i - i);
}


void subdivide_integer () {
  int y;
  short z = v;
  int k = (z+675) * (z+675);
  int l = (z+17817) * (z+17817);

  int x = sizeof(y)+sizeof(y); // do not optimize y
  int *p = &x + x; // do not optmize x;

  long long i1 = vs;
  long long i2 = vs;
  long long r = i1 * i1 + (i2+3) * (i2+3); // (i2+3) not fully precise with 14 subdivisions

  int t[102];
  short idx = vs;
  //@ assert 0 <= idx <= 10;
  t[idx*idx] = 1;
}


/* Exemples where a subdivision on several variables simultaneously is necessary
   to get more precision. */
void subdivide_several_variables () {
  int w = Frama_C_interval(-10, 10);
  int x = Frama_C_interval(-10, 10);
  int y = Frama_C_interval(-10, 10);
  int z = Frama_C_interval(-10, 10);
  /* A subdivision on each variable separately is more efficient here. */
  int norm = x * x + y * y;
  /* Subdivide on x, then on y. Note that the subdivision on x does not improve
     the result but only the value of x*x, while the later subdivision on y
     improve the value of the result thanks to the reduced value of x*x. */
  int mult = ((x*x)*y)*y;
  /* A subdivision on both variables is more efficient here. */
  int zero = x * y - y * x;
  /* Both square and square2 should be subdivided in the same way, even if [x]
     only appears in [x*x - 2xy] in the first expression. */
  int square = x*x - 2*x*y + y*y;
  int square2 = x*x + y*y - 2*x*y;
  /* Subdivision on the three variables x, y, z, and on w. */
  int res = (z*x + x*y + y*z) + w * w;
}

int table[] = {
  0x42, 0x42, 0x42, 0x42,
  1, 8, 7, 2,
  0x00, 0x00, 0x00, 0x00,
  0x42, 0x42, 0x42, 0x42,
  9, 3, 4, 5,
  0x00, 0x00, 0x00, 0x00,
  0x42, 0x42, 0x42, 0x42,
  2, 3, 7, 5,
  0x00, 0x00, 0x00, 0x00
};

/* This example illustrates the need to evaluate the complete expression (and
   not some subexpression) to be able to reduce it. */
void subdivide_table () {
  int x = 0;
  /*@ loop invariant x < 10; */
  while (1)
    x = table[4 + (((x>>2)*3)<<2) + (x%4)];
}

/* When subdividing on a lvalue that has been reduced by the forward evaluation,
   beware to not forget the alarms that led to its reduction. */
void subdivide_reduced_value () {
  int t1[2] = {0, 1};
  int t2[2] = {0, 1};
  int i = v;
  /* Subdivision on i, that has been reduced to {0; 1}. Alarms about array index
     must be emitted. Ideally, the value computed for the result would be zero, 
     even with few subdivisions. */
  int r = t1[i] - t2[i];
}

/* Tests local subdivision via option -eva-subdivide-non-linear-function
   and annotations subdivide. */
void local_subdivide () {
  int x = Frama_C_interval(-10, 10);
  int y = Frama_C_interval(-10, 10);
  /*@ subdivide 0; */
  int imprecise = x*x - 2*x*y + y*y;          // No subdivision: [-400..400]
  /*@ subdivide 14; */
  int more_precise = x*x - 2*x*y + y*y;       // Some subdivisions: [-48..400]
  int even_more_precise = x*x - 2*x*y + y*y;  // Local subdivision: [-16..400]
  /*@ subdivide 100; */
  int precise = x*x - 2*x*y + y*y;            // Maximal subdivision: [0..400]
}

void main () {
  subdivide_integer ();
  subdivide_pointer ();
  subdivide_several_variables ();
  if (v) subdivide_table ();
  subdivide_reduced_value ();
  local_subdivide ();
}
