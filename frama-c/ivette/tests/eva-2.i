volatile int nondet;

void fun () {
  int x = nondet;
  x = -x;
}

void yet_another () {
  int x = nondet;
  fun ();
  int y = 100 / x;
}

void main () {
  fun ();
  /*@ assert boh: 1 == 1; */
  yet_another ();
  int i = 0;
  /*@ assert user: i == 0; */
}
