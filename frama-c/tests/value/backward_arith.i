/* run.config*
   STDOPT: +"-keep-logical-operators"
*/

/* Test the soundness of arithmetic backward propagators.  */

volatile int nondet;

void unsigned_neg () {
  unsigned int x = nondet;
  unsigned int minus_ten = -10; /* minus_ten = 4294967286. */
  if (-x == minus_ten)
    Frama_C_show_each_ten(x);
  else
    Frama_C_show_each_not_ten(x);
  if (-x < minus_ten)
    Frama_C_show_each_greater_than_ten_or_zero(x);
  else
    Frama_C_show_each_smaller_than_ten_but_zero(x);
  if (-x == 10)
    Frama_C_show_each_minus_ten(x); /* 4294967286 */
  else
    Frama_C_show_each_not_minus_ten(x);  /* not 4294967286 */
  if (-x < 10)
    Frama_C_show_each_greater_than_minus_ten_or_zero(x); /* > 4294967286 or 0 */
  else
    Frama_C_show_each_smaller_than_minus_ten_but_zero(x); /* <= 4294967286 but 0 */
}

void logical_operators () {
  unsigned int x = nondet;
  unsigned int y = nondet;
  unsigned int a = x % 10;
  unsigned int b = x % 10;

  // Logical conjunction LAnd.
  if (x < 11 && y < 21)
    Frama_C_show_each("0..10", x, "0..20", y);
  else
    Frama_C_show_each("top", x, "top", y);
  if (a < 10 && y < 10)
    Frama_C_show_each("0..9", a, "0..9", y);
  else
    Frama_C_show_each("0..9", a, "10..max", y);
  if (a > 10 && y < 10)
    Frama_C_show_each("bottom", a, y);
  else
    Frama_C_show_each("0..9", a, "top", y);
  if (a > 10 && b > 10)
    Frama_C_show_each("bottom", a, b);
  else
    Frama_C_show_each("0..9", a, "0..9", b);

  // Logical disjunction LOr.
  if (x > 10 || y > 20)
    Frama_C_show_each("top", x, "top", y);
  else
    Frama_C_show_each("0..10", x, "0..20", y);
  if (a > 10 || y > 10)
    Frama_C_show_each("0..9", a, "11..max", y);
  else
    Frama_C_show_each("0..9", a, "0..10", y);
  if (a < 10 || y > 10)
    Frama_C_show_each("0..9", a, "top", y);
  else
    Frama_C_show_each("bottom", a, y);
  if (a > 10 || b > 10)
    Frama_C_show_each("bottom", a, b);
  else
    Frama_C_show_each("0..9", a, "0..9", b);
}


int main () {
  unsigned_neg ();
  logical_operators ();
  return 0;
}
