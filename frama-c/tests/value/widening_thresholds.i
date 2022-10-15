/* run.config*
  STDOPT: +""
*/

/* Tests the inference of widening thresholds. */

volatile int nondet;
static int g;

void incr_modulo (void) {
  g = (g + 1) % 1000;
}

/* Tests the inference of widening thresholds according to modulo operations. */
void modulo (void) {
  short s = 0;
  int i = 17;
  while (nondet) {
    s = (s + 1) % 10;
    i = (i + 3) % 100;
    incr_modulo();
  }
}

void main (void) {
  modulo();
}
