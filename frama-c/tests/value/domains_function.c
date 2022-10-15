/* run.config*
   STDOPT: #"-eva-domains-function symbolic-locations:infer+w,symbolic-locations:use+r,symbolic-locations:test_propagation-,symbolic-locations:enabled,symbolic-locations:disabled-,symbolic-locations:recursively_enabled+"
*/

#include <__fc_builtin.h>

/* Tests the -eva-domains-function option that enables a domain for the given
   functions. This test uses the symbolic locations domain to store the value
   of the location t[i] where [i] is imprecise, from an assignment of t[i]
   to a read of t[i].
   If the domain is not enabled, the value of t[i] remains imprecise because
   [i] is imprecise. If the domain is enabled, the value of the first assignemnt
   is stored until the read. If the assignment and the read are in different
   functions, the domain should also be enabled in all functions in between. */

volatile int undet;
int i, result, t[10];

/* No interaction with the known properties about t[i]. */
void nothing () {
  int tmp = t[i] - t[0];
}

/* Modify the value of t[i]. */
void kill () {
  t[0] = undet;
}

/* The domain has write access on this function: it infers the value of t[i]. */
void infer () {
  t[i] = 42;
}

/* The domain has no write access on this function. */
void no_infer () {
  t[i] = 42;
}

/* The domain has read access on this function: it can use the value of t[i]. */
void use () {
  result = t[i];
}

/* The domain has no read access on this function. */
void no_use () {
  result = t[i];
}

/* Test the propagation of information about t[i] from function [infer]
   to function [use]. All other combinations of functions should not be
   precise. */
void test_propagation () {
  infer ();
  no_use ();
  Frama_C_show_each_top(result);
  nothing ();
  use ();
  Frama_C_show_each_singleton(result);
  kill ();
  use ();
  Frama_C_show_each_top(result);
  no_infer ();
  use ();
  Frama_C_show_each_top(result);
}

/* The domain is enabled on this function. */
void enabled () {
  t[i] = 0;
  result = t[i];
}

/* The domain is not enabled on this function. */
void not_enabled () {
  t[i] = 1;
  result = t[i];
  Frama_C_show_each_top(result);
}

/* The domain is disabled on this function. */
void disabled () {
  t[i] = 2;
  result = t[i];
  Frama_C_show_each_top(result);
}

/* Precise result only after [enabled], since it is the only function
   where the domain is enabled. */
void test () {
  t[i] = 3;
  result = t[i];
  Frama_C_show_each_top(result);
  enabled ();
  Frama_C_show_each_singleton(result);
  not_enabled ();
  Frama_C_show_each_top(result);
  disabled ();
  Frama_C_show_each_top(result);
}

/* The domain is recursively enabled in this function and all functions called
   from it: the results should be precise, except after [disabled] where the
   domain is specifically disabled.*/
void recursively_enabled () {
  t[i] = 4;
  result = t[i];
  Frama_C_show_each_singleton(result);
  enabled ();
  Frama_C_show_each_singleton(result);
  not_enabled ();
  Frama_C_show_each_singleton(result);
  disabled ();
  Frama_C_show_each_top(result);
}

void main () {
  for (int j = 0; j < 10; j++)
    t[j] = undet;
  i = Frama_C_interval(0,9);
  test ();
  recursively_enabled ();
  test_propagation ();
}
