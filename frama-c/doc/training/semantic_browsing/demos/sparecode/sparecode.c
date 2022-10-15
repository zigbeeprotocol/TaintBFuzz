/* Waiting for results such as:
 * spare code analysis removes statements having variables with
 * prefix "spare_"
 *
 * slicing analysis removes statement having variables with
 * prefix "spare_" and "any_"
 */

int G;

int tmp (int a) {
  int x = a;
  /*@ assert x == a ; */
  int w = 1;
  /* w is not spare (otherwise the assertion should be removed) */
  /*@ assert w == 1 ; */
  int spare_z = 1;
  int spare_y = a+spare_z;
  return x;
}

int param (int a, int spare_b) {
  return a;
}

int spare_called_fct (int a) {
  return a;
}

int two_outputs (int a, int b) {
  G += b;
  return a;
}

int call_two_outputs (void) {
  int x, spare_y;
  int any_b = 1;
  int any_a = 2;
  int a = 1;
  int b = any_b;
  x = two_outputs (a, b);
  G = 1;
  b = 2;
  a = any_a;
  spare_y = two_outputs (a, b);
  return x;
}

void assign (int *p, int *q) {
  *p = *q ;
}

int loop (int x, int y, int z) {
  int i = 0;
  /*@ assert i < z ; */
  /*@ loop invariant i < y ; */
  while (i < x) {
    i ++;
  }
  return i;
}

void stop(void) __attribute__ ((noreturn)) ;

int main (int noreturn, int halt) {
  int res = 0;
  int spare_tmp = 3;
  int spare_param = 2 + spare_tmp;
  int x = 1;
  int y = 2;
  res += param (2, spare_param);
  res += tmp (4);
  spare_called_fct (5);
  res += call_two_outputs ();
  res += loop (10, 15, 20);
  assign (&x, &y) ;
  if (noreturn) {
    if (halt)
      stop () ;
    else
      while (1);
    }

  return res + G + x;
}
