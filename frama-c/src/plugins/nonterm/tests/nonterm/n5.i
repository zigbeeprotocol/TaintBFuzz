volatile int nondet;

// definitely non-terminating => warning
/*@ ensures \false; */
void never_terminates(void);

// possibly non-terminating => no warning
/*@ terminates \false; */
void may_not_terminate(void);

void f() {
  never_terminates();
}

// g is not reachable => no warning
void g() {
  never_terminates();
}

void main() {
  may_not_terminate();
  if (nondet) f();
  never_terminates();
  g();
}
