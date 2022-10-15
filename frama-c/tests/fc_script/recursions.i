/* run.config
   NOFRAMAC: testing frama-c-script, not frama-c itself
   EXECNOW: LOG recursions.res LOG recursions.err PTESTS_TESTING=1 %{bin:frama-c-script} heuristic-detect-recursion @PTEST_FILE@ > @PTEST_RESULT@/recursions.res 2> @PTEST_RESULT@/recursions.err
*/

volatile int v;

void g() {
  int g = 42;
}

void f() {
  if (v) f();
  else g();
}

void h() {
  if (v) h();
  else g();
}

void i() {
  g();
}

void j() {
  f();
}

void l(void);
void m(void);

void k() {
  if (v) l();
}

void l() {
  if (v) m();
}

void m() {
  if (v) k();
}

void norec() {
}

int direct_rec() {
  return direct_rec();
}

void indirect_rec1();

void indirect_rec2() {
  indirect_rec1();
}

void indirect_rec1() {
  indirect_rec2();
}

void decl_only();

void one_liner_function() { decl_only(); }

void multiple_indirect1();

void multiple_indirect2() {
  multiple_indirect1();
  multiple_indirect1();
}

void multiple_indirect1() {
  multiple_indirect2();
  multiple_indirect2();
}
